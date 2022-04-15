//
// Copyright 2022 FRAGATA COMPUTER SYSTEMS AG
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

package core

import (
    "fmt"
    "io"
)

//
//    Private constants
//

const (
    GP_MAX = 6
    FP_MAX = 8
)

//
//    Configuration variables
//

var (
    optFcommon bool // default = true
    optFpic bool
)

//
//    Private state variables
//

var (
    outputFile io.Writer
    depth int
    genCurrentFn *Obj
    countNext int
)

//
//    Initialization
//

func InitCodegen(opt *Options) {
    optFcommon = opt.OptFcommon
    optFpic = opt.OptFpic
    outputFile = nil
    depth = 0
    genCurrentFn = nil
    countNext = 1
}

//
//    Private immutable data
//

var (
    argreg8 = []string{"%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b"}
    argreg16 = []string{"%di", "%si", "%dx", "%cx", "%r8w", "%r9w"}
    argreg32 = []string{"%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"}
    argreg64 = []string{"%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"}
)

//
//    Private functions
//

func println(format string, args ...interface{}) {
    fmt.Fprintf(outputFile, format, args...)
    fmt.Fprintf(outputFile, "\n")
}

func count() int {
    i := countNext
    countNext++
    return i
}

func push() {
    println("  push %%rax")
    depth++
}

func pop(arg string) {
    println("  pop %s", arg)
    depth--
}

func pushf() {
    println("  sub $8, %%rsp")
    println("  movsd %%xmm0, (%%rsp)")
    depth++
}

func popf(reg int) {
    println("  movsd (%%rsp), %%xmm%d", reg)
    println("  add $8, %%rsp")
    depth--
}
 
func regDx(sz int) string{
    switch sz {
    case 1: 
        return "%dl"
    case 2: 
        return "%dx"
    case 4: 
        return "%edx"
    case 8: 
        return "%rdx"
    }
    Unreachable()
    return ""
}

func regAx(sz int) string {
    switch (sz) {
    case 1: 
        return "%al"
    case 2: 
        return "%ax"
    case 4: 
        return "%eax"
    case 8: 
        return "%rax"
    }
    Unreachable()
    return ""
} 

// Computes the absolute address of a given node.
// It's an error if a given node does not reside in memory.
func genAddr(node *Node) {
    switch node.kind {
    case ND_VAR:
        // Variable-length array, which is always local.
        if node.sym.ty.kind == TY_VLA {
            println("  mov %d(%%rbp), %%rax", node.sym.offset)
            return
        }

        // Local variable
        if node.sym.isLocal {
            println("  lea %d(%%rbp), %%rax", node.sym.offset)
            return
        }

        if optFpic {
            // Thread-local variable
            if node.sym.isTls {
                println("  data16 lea %s@tlsgd(%%rip), %%rdi", node.sym.name)
                println("  .value 0x6666")
                println("  rex64")
                println("  call __tls_get_addr@PLT")
                return
            }

            // Function or global variable
            println("  mov %s@GOTPCREL(%%rip), %%rax", node.sym.name)
            return
        }

        // Thread-local variable
        if node.sym.isTls {
            println("  mov %%fs:0, %%rax")
            println("  add $%s@tpoff, %%rax", node.sym.name)
            return
        }

        // Here, we generate an absolute address of a function or a global
        // variable. Even though they exist at a certain address at runtime,
        // their addresses are not known at link-time for the following
        // two reasons.
        //
        //  - Address randomization: Executables are loaded to memory as a
        //    whole but it is not known what address they are loaded to.
        //    Therefore, at link-time, relative address in the same
        //    exectuable (i.e. the distance between two functions in the
        //    same executable) is known, but the absolute address is not
        //    known.
        //
        //  - Dynamic linking: Dynamic shared objects (DSOs) or .so files
        //    are loaded to memory alongside an executable at runtime and
        //    linked by the runtime loader in memory. We know nothing
        //    about addresses of global stuff that may be defined by DSOs
        //    until the runtime relocation is complete.
        //
        // In order to deal with the former case, we use RIP-relative
        // addressing, denoted by `(%rip)`. For the latter, we obtain an
        // address of a stuff that may be in a shared object file from the
        // Global Offset Table using `@GOTPCREL(%rip)` notation.

        // Function
        if node.ty.kind == TY_FUNC {
            if node.sym.isDefinition {
                println("  lea %s(%%rip), %%rax", node.sym.name)
            } else {
                println("  mov %s@GOTPCREL(%%rip), %%rax", node.sym.name)
            }
            return
        }

        // Global variable
        println("  lea %s(%%rip), %%rax", node.sym.name)
        return
    case ND_DEREF:
        genExpr(node.lhs)
        return
    case ND_COMMA:
        genExpr(node.lhs)
        genAddr(node.rhs)
        return
    case ND_MEMBER:
        genAddr(node.lhs)
        println("  add $%d, %%rax", node.member.offset)
        return
    case ND_FUNCALL:
        if node.retBuffer != nil {
            genExpr(node)
            return
        }
        // break
    case ND_ASSIGN, ND_COND:
        if node.ty.kind == TY_STRUCT || node.ty.kind == TY_UNION {
            genExpr(node)
            return
        }
        // break
    case ND_VLA_PTR:
        println("  lea %d(%%rbp), %%rax", node.sym.offset)
        return
    }

    ErrorTok(node.tok, "not an lvalue")
}

// Loads a value from where %rax is pointing to.
func load(ty *Type) {
    switch ty.kind {
    case TY_ARRAY, TY_STRUCT, TY_UNION, TY_FUNC, TY_VLA:
        // If it is an array, do not attempt to load a value to the
        // register because in general we can't load an entire array to a
        // register. As a result, the result of an evaluation of an array
        // becomes not the array itself but the address of the array.
        // This is where "array is automatically converted to a pointer to
        // the first element of the array in C" occurs.
        return
    case TY_FLOAT:
        println("  movss (%%rax), %%xmm0")
        return
    case TY_DOUBLE:
        println("  movsd (%%rax), %%xmm0")
        return
    case TY_LDOUBLE:
        println("  fldt (%%rax)")
        return
    }

    var insn string
    if ty.isUnsigned {
        insn = "movz"
    } else {
        insn = "movs"
    }

    // When we load a char or a short value to a register, we always
    // extend them to the size of int, so we can assume the lower half of
    // a register always contains a valid value. The upper half of a
    // register for char, short and int may contain garbage. When we load
    // a long value to a register, it simply occupies the entire register.
    switch ty.size {
    case 1:
        println("  %sbl (%%rax), %%eax", insn)
    case 2:
        println("  %swl (%%rax), %%eax", insn)
    case 4:
        println("  movsxd (%%rax), %%rax")
    default:
        println("  mov (%%rax), %%rax")
    } 
}

// Stores %rax to an address that the stack top is pointing to.
func store(ty *Type) {
    pop("%rdi")

    switch ty.kind {
    case TY_STRUCT, TY_UNION:
        for i := 0; i < ty.size; i++ {
            println("  mov %d(%%rax), %%r8b", i)
            println("  mov %%r8b, %d(%%rdi)", i)
        }
        return
    case TY_FLOAT:
        println("  movss %%xmm0, (%%rdi)")
        return
    case TY_DOUBLE:
        println("  movsd %%xmm0, (%%rdi)")
        return
    case TY_LDOUBLE:
        println("  fstpt (%%rdi)")
        return
    }

    switch ty.size {
    case 1:
        println("  mov %%al, (%%rdi)")
    case 2:
        println("  mov %%ax, (%%rdi)")
    case 4:
        println("  mov %%eax, (%%rdi)")
    default:
        println("  mov %%rax, (%%rdi)")
    }
}

func cmpZero(ty *Type) {
    switch ty.kind {
    case TY_FLOAT:
        println("  xorps %%xmm1, %%xmm1")
        println("  ucomiss %%xmm1, %%xmm0")
        return
    case TY_DOUBLE:
        println("  xorpd %%xmm1, %%xmm1")
        println("  ucomisd %%xmm1, %%xmm0")
        return
    case TY_LDOUBLE:
        println("  fldz")
        println("  fucomip")
        println("  fstp %%st(0)")
        return
    }

    if IsInteger(ty) && ty.size <= 4 {
        println("  cmp $0, %%eax")
    } else {
        println("  cmp $0, %%rax")
    }
} 

const (
    I8 int = iota 
    I16 
    I32 
    I64 
    U8 
    U16 
    U32 
    U64 
    F32 
    F64 
    F80
)

func getTypeId(ty *Type) int {
    switch ty.kind {
    case TY_CHAR:
        if ty.isUnsigned {
            return U8
        } else {
            return I8
        }
    case TY_SHORT:
        if ty.isUnsigned {
            return U16
        } else {
            return I16
        }
    case TY_INT:
        if ty.isUnsigned {
            return U32
        } else {
            return I32
        }
    case TY_LONG:
        if ty.isUnsigned {
            return U64
        } else {
            return I64
        }
    case TY_FLOAT:
        return F32
    case TY_DOUBLE:
        return F64
    case TY_LDOUBLE:
        return F80
    }
    return U64
} 

// The table for type casts

const (
    i32i8 = "movsbl %al, %eax"
    i32u8 = "movzbl %al, %eax"
    i32i16 = "movswl %ax, %eax"
    i32u16 = "movzwl %ax, %eax"
    i32f32 = "cvtsi2ssl %eax, %xmm0"
    i32i64 = "movsxd %eax, %rax"
    i32f64 = "cvtsi2sdl %eax, %xmm0"
    i32f80 = "mov %eax, -4(%rsp); fildl -4(%rsp)"

    u32f32 = "mov %eax, %eax; cvtsi2ssq %rax, %xmm0"
    u32i64 = "mov %eax, %eax"
    u32f64 = "mov %eax, %eax; cvtsi2sdq %rax, %xmm0"
    u32f80 = "mov %eax, %eax; mov %rax, -8(%rsp); fildll -8(%rsp)"

    i64f32 = "cvtsi2ssq %rax, %xmm0"
    i64f64 = "cvtsi2sdq %rax, %xmm0"
    i64f80 = "movq %rax, -8(%rsp); fildll -8(%rsp)"

    u64f32 = "cvtsi2ssq %rax, %xmm0"
    u64f64 =
        "test %rax,%rax; js 1f; pxor %xmm0,%xmm0; cvtsi2sd %rax,%xmm0; jmp 2f; " +
        "1: mov %rax,%rdi; and $1,%eax; pxor %xmm0,%xmm0; shr %rdi; " +
        "or %rax,%rdi; cvtsi2sd %rdi,%xmm0; addsd %xmm0,%xmm0; 2:"
    u64f80 =
        "mov %rax, -8(%rsp); fildq -8(%rsp); test %rax, %rax; jns 1f;" +
        "mov $1602224128, %eax; mov %eax, -4(%rsp); fadds -4(%rsp); 1:"

    f32i8 = "cvttss2sil %xmm0, %eax; movsbl %al, %eax"
    f32u8 = "cvttss2sil %xmm0, %eax; movzbl %al, %eax"
    f32i16 = "cvttss2sil %xmm0, %eax; movswl %ax, %eax"
    f32u16 = "cvttss2sil %xmm0, %eax; movzwl %ax, %eax"
    f32i32 = "cvttss2sil %xmm0, %eax"
    f32u32 = "cvttss2siq %xmm0, %rax"
    f32i64 = "cvttss2siq %xmm0, %rax"
    f32u64 = "cvttss2siq %xmm0, %rax"
    f32f64 = "cvtss2sd %xmm0, %xmm0"
    f32f80 = "movss %xmm0, -4(%rsp); flds -4(%rsp)"

    f64i8 = "cvttsd2sil %xmm0, %eax; movsbl %al, %eax"
    f64u8 = "cvttsd2sil %xmm0, %eax; movzbl %al, %eax"
    f64i16 = "cvttsd2sil %xmm0, %eax; movswl %ax, %eax"
    f64u16 = "cvttsd2sil %xmm0, %eax; movzwl %ax, %eax"
    f64i32 = "cvttsd2sil %xmm0, %eax"
    f64u32 = "cvttsd2siq %xmm0, %rax"
    f64i64 = "cvttsd2siq %xmm0, %rax"
    f64u64 = "cvttsd2siq %xmm0, %rax"
    f64f32 = "cvtsd2ss %xmm0, %xmm0"
    f64f80 = "movsd %xmm0, -8(%rsp); fldl -8(%rsp)"

    FROM_F80_1 =
        "fnstcw -10(%rsp); movzwl -10(%rsp), %eax; or $12, %ah; " +
        "mov %ax, -12(%rsp); fldcw -12(%rsp); "

    FROM_F80_2 = " -24(%rsp); fldcw -10(%rsp); "

    f80i8 = FROM_F80_1 + "fistps" + FROM_F80_2 + "movsbl -24(%rsp), %eax"
    f80u8 = FROM_F80_1 + "fistps" + FROM_F80_2 + "movzbl -24(%rsp), %eax"
    f80i16 = FROM_F80_1 + "fistps" + FROM_F80_2 + "movzbl -24(%rsp), %eax"
    f80u16 = FROM_F80_1 + "fistpl" + FROM_F80_2 + "movswl -24(%rsp), %eax"
    f80i32 = FROM_F80_1 + "fistpl" + FROM_F80_2 + "mov -24(%rsp), %eax"
    f80u32 = FROM_F80_1 + "fistpl" + FROM_F80_2 + "mov -24(%rsp), %eax"
    f80i64 = FROM_F80_1 + "fistpq" + FROM_F80_2 + "mov -24(%rsp), %rax"
    f80u64 = FROM_F80_1 + "fistpq" + FROM_F80_2 + "mov -24(%rsp), %rax"
    f80f32 = "fstps -8(%rsp); movss -8(%rsp), %xmm0"
    f80f64 = "fstpl -8(%rsp); movsd -8(%rsp), %xmm0"
)

// string[11][11]
var castTable = [...]string{
    // i8   i16     i32     i64     u8     u16     u32     u64     f32     f64     f80
    "",    "",     "",     i32i64, i32u8, i32u16, "",     i32i64, i32f32, i32f64, i32f80, // i8
    i32i8, "",     "",     i32i64, i32u8, i32u16, "",     i32i64, i32f32, i32f64, i32f80, // i16
    i32i8, i32i16, "",     i32i64, i32u8, i32u16, "",     i32i64, i32f32, i32f64, i32f80, // i32
    i32i8, i32i16, "",     "",     i32u8, i32u16, "",     "",     i64f32, i64f64, i64f80, // i64

    i32i8, "",     "",     i32i64, "",    "",     "",     i32i64, i32f32, i32f64, i32f80, // u8
    i32i8, i32i16, "",     i32i64, i32u8, "",     "",     i32i64, i32f32, i32f64, i32f80, // u16
    i32i8, i32i16, "",     u32i64, i32u8, i32u16, "",     u32i64, u32f32, u32f64, u32f80, // u32
    i32i8, i32i16, "",     "",     i32u8, i32u16, "",     "",     u64f32, u64f64, u64f80, // u64

    f32i8, f32i16, f32i32, f32i64, f32u8, f32u16, f32u32, f32u64, "",     f32f64, f32f80, // f32
    f64i8, f64i16, f64i32, f64i64, f64u8, f64u16, f64u32, f64u64, f64f32, "",     f64f80, // f64
    f80i8, f80i16, f80i32, f80i64, f80u8, f80u16, f80u32, f80u64, f80f32, f80f64, "",     // f80
}

func genCast(from *Type, to *Type) {
    if to.kind == TY_VOID {
        return
    }

    if to.kind == TY_BOOL {
        cmpZero(from)
        println("  setne %%al")
        println("  movzx %%al, %%eax")
        return
    }

    t1 := getTypeId(from)
    t2 := getTypeId(to)
    inst := castTable[t1*11+t2]
    if len(inst) != 0 {
        println("  %s", inst)
    }
} 

// Structs or unions equal or smaller than 16 bytes are passed
// using up to two registers.
//
// If the first 8 bytes contains only floating-point type members,
// they are passed in an XMM register. Otherwise, they are passed
// in a general-purpose register.
//
// If a struct/union is larger than 8 bytes, the same rule is
// applied to the the next 8 byte chunk.
//
// This function returns true if `ty` has only floating-point
// members in its byte range [lo, hi).
func hasFlonum(ty *Type, lo int, hi int, offset int) bool {
    if ty.kind == TY_STRUCT || ty.kind == TY_UNION {
        for mem := ty.members; mem != nil; mem = mem.next {
            if !hasFlonum(mem.ty, lo, hi, offset+mem.offset) {
                return false
            }
        }
        return true
    }

    if ty.kind == TY_ARRAY {
        for i := 0; i < ty.arrayLen; i++ {
            if !hasFlonum(ty.base, lo, hi, offset+ty.base.size*i) {
                return false
            }
        return true
        }
    }

  return (offset < lo || hi <= offset || ty.kind == TY_FLOAT || ty.kind == TY_DOUBLE)
}

func hasFlonum1(ty *Type) bool {
    return hasFlonum(ty, 0, 8, 0)
}

func hasFlonum2(ty *Type) bool {
    return hasFlonum(ty, 8, 16, 0)
}

func pushStruct(ty *Type) {
    sz := AlignTo(ty.size, 8)
    println("  sub $%d, %%rsp", sz)
    depth += sz / 8

    for i := 0; i < ty.size; i++ {
        println("  mov %d(%%rax), %%r10b", i)
        println("  mov %%r10b, %d(%%rsp)", i)
    }
}

func pushArgs2(args *Node, firstPass bool) {
    if args == nil {
        return
    }
    pushArgs2(args.next, firstPass)

    if (firstPass && !args.passByStack) || (!firstPass && args.passByStack) {
        return
    }

    genExpr(args)

    switch args.ty.kind {
    case TY_STRUCT, TY_UNION:
        pushStruct(args.ty)
    case TY_FLOAT, TY_DOUBLE:
        pushf()
    case TY_LDOUBLE:
        println("  sub $16, %%rsp")
        println("  fstpt (%%rsp)")
        depth += 2
    default:
        push()
    }
}

// Load function call arguments. Arguments are already evaluated and
// stored to the stack as local variables. What we need to do in this
// function is to load them to registers or push them to the stack as
// specified by the x86-64 psABI. Here is what the spec says:
//
// - Up to 6 arguments of integral type are passed using RDI, RSI,
//   RDX, RCX, R8 and R9.
//
// - Up to 8 arguments of floating-point type are passed using XMM0 to
//   XMM7.
//
// - If all registers of an appropriate type are already used, push an
//   argument to the stack in the right-to-left order.
//
// - Each argument passed on the stack takes 8 bytes, and the end of
//   the argument area must be aligned to a 16 byte boundary.
//
// - If a function is variadic, set the number of floating-point type
//   arguments to RAX.
func pushArgs(node *Node) int {
    stack := 0
    gp := 0
    fp := 0

    // If the return type is a large struct/union, the caller passes
    // a pointer to a buffer as if it were the first argument.
    if node.retBuffer != nil && node.ty.size > 16 {
        gp++
    }

    // Load as many arguments to the registers as possible.
    for arg := node.args; arg != nil; arg = arg.next {
        ty := arg.ty

        switch ty.kind {
        case TY_STRUCT, TY_UNION:
            if ty.size > 16 {
                arg.passByStack = true
                stack += AlignTo(ty.size, 8) / 8
            } else {
                fp1 := 0
                if hasFlonum1(ty) {
                    fp1 = 1
                }
                fp2 := 0
                if hasFlonum2(ty) {
                    fp2 = 1
                }

                if fp + fp1 + fp2 < FP_MAX && gp + (1 - fp1) + (1 - fp2) < GP_MAX {
                    fp = fp + fp1 + fp2
                    gp = gp + (1 - fp1) + (1 - fp2)
                } else {
                    arg.passByStack = true
                    stack += AlignTo(ty.size, 8) / 8
                }
            }
        case TY_FLOAT, TY_DOUBLE:
            if fp >= FP_MAX {
                arg.passByStack = true
                stack++
            }
            fp++
        case TY_LDOUBLE:
            arg.passByStack = true
            stack += 2
        default:
            if gp >= GP_MAX {
                arg.passByStack = true
                stack++
            }
            gp++
        }
    }

    if (depth + stack) % 2 == 1 {
        println("  sub $8, %%rsp")
        depth++
        stack++
    }

    pushArgs2(node.args, true)
    pushArgs2(node.args, false)

    // If the return type is a large struct/union, the caller passes
    // a pointer to a buffer as if it were the first argument.
    if node.retBuffer != nil && node.ty.size > 16 {
        println("  lea %d(%%rbp), %%rax", node.retBuffer.offset)
        push()
    }

    return stack
}

func copyRetBuffer(sym *Obj) {
    ty := sym.ty
    gp := 0
    fp := 0

    if hasFlonum1(ty) {
        Assert(ty.size == 4 || 8 <= ty.size)
        if ty.size == 4 {
            println("  movss %%xmm0, %d(%%rbp)", sym.offset)
        } else {
            println("  movsd %%xmm0, %d(%%rbp)", sym.offset)
        }
        fp++
    } else {
        for i := 0; i < IntMin(8, ty.size); i++ {
            println("  mov %%al, %d(%%rbp)", sym.offset+i)
            println("  shr $8, %%rax")
        }
        gp++
    }

    if ty.size > 8 {
        if hasFlonum2(ty) {
            Assert(ty.size == 12 || ty.size == 16)
            if ty.size == 12 {
                println("  movss %%xmm%d, %d(%%rbp)", fp, sym.offset+8)
            } else {
                println("  movsd %%xmm%d, %d(%%rbp)", fp, sym.offset+8)
            }
        } else {
            var reg1, reg2 string
            if gp == 0 {
                reg1 = "%al"
                reg2 = "%rax"
            } else {
                reg1 = "%dl"
                reg2 = "%rdx"
            }
            for i := 8; i < IntMin(16, ty.size); i++ {
                println("  mov %s, %d(%%rbp)", reg1, sym.offset+i)
                println("  shr $8, %s", reg2)
            }
        }
    }
}

func copyStructReg() {
    ty := genCurrentFn.ty.returnTy
    gp := 0
    fp := 0

    println("  mov %%rax, %%rdi")

    if hasFlonum(ty, 0, 8, 0) {
        Assert(ty.size == 4 || 8 <= ty.size)
        if ty.size == 4 {
            println("  movss (%%rdi), %%xmm0")
        } else {
            println("  movsd (%%rdi), %%xmm0")
        }
        fp++
    } else {
        println("  mov $0, %%rax")
        for i := IntMin(8, ty.size) - 1; i >= 0; i-- {
            println("  shl $8, %%rax")
            println("  mov %d(%%rdi), %%al", i)
        }
        gp++
    }

    if ty.size > 8 {
        if hasFlonum(ty, 8, 16, 0) {
            Assert(ty.size == 12 || ty.size == 16)
            if ty.size == 4 {
                println("  movss 8(%%rdi), %%xmm%d", fp);
            } else {
                println("  movsd 8(%%rdi), %%xmm%d", fp)
            }
        } else {
            var reg1, reg2 string
            if gp == 0 {
                reg1 = "%al"
                reg2 = "%rax"
            } else {
                reg1 = "%dl"
                reg2 = "%rdx"
            }
            println("  mov $0, %s", reg2)
            for i := IntMin(16, ty.size) - 1; i >= 8; i-- {
                println("  shl $8, %s", reg2)
                println("  mov %d(%%rdi), %s", i, reg1)
            }
        }
    }
} 

func copyStructMem() {
    ty := genCurrentFn.ty.returnTy
    sym := genCurrentFn.params

    println("  mov %d(%%rbp), %%rdi", sym.offset)

    for i := 0; i < ty.size; i++ {
        println("  mov %d(%%rax), %%dl", i)
        println("  mov %%dl, %d(%%rdi)", i)
    }
}

func genBuiltinAlloca() {
    // Align size to 16 bytes.
    println("  add $15, %%rdi")
    println("  and $0xfffffff0, %%edi")

    // Shift the temporary area by %rdi.
    println("  mov %d(%%rbp), %%rcx", genCurrentFn.allocaBottom.offset)
    println("  sub %%rsp, %%rcx")
    println("  mov %%rsp, %%rax")
    println("  sub %%rdi, %%rsp")
    println("  mov %%rsp, %%rdx")
    println("1:")
    println("  cmp $0, %%rcx")
    println("  je 2f")
    println("  mov (%%rax), %%r8b")
    println("  mov %%r8b, (%%rdx)")
    println("  inc %%rdx")
    println("  inc %%rax")
    println("  dec %%rcx")
    println("  jmp 1b")
    println("2:")

    // Move alloca_bottom pointer.
    println("  mov %d(%%rbp), %%rax", genCurrentFn.allocaBottom.offset)
    println("  sub %%rdi, %%rax")
    println("  mov %%rax, %d(%%rbp)", genCurrentFn.allocaBottom.offset)
}

// Generates code for a given node.
func genExpr(node *Node) { 
    println("  .loc %d %d", node.tok.file.fileNo, node.tok.lineNo)

    switch node.kind {
    case ND_NULL_EXPR:
        return
    case ND_NUM:
        switch node.ty.kind {
        case TY_FLOAT:
/* TODO: Remove this
            union { float f32; uint32_t u32; } u = { node.fval };
            println("  mov $%u, %%eax  # float %Lf", u.u32, node.fval)
            println("  movq %%rax, %%xmm0")
*/
            u32 := x64Float32ToBinary(node.fval)
            println("  mov $%u, %%eax  # float %Lf", u32, node.fval)
            println("  movq %%rax, %%xmm0")
            return
        case TY_DOUBLE:
/* TODO: Remove this
            union { double f64; uint64_t u64; } u = { node.fval };
            println("  mov $%lu, %%rax  # double %Lf", u.u64, node.fval)
            println("  movq %%rax, %%xmm0")
*/
            u64 := x64Float32ToBinary(node.fval)
            println("  mov $%u, %%rax  # double %Lf", u64, node.fval)
            println("  movq %%rax, %%xmm0")
            return
        case TY_LDOUBLE:
/* TODO: Remove this
            union { long double f80; uint64_t u64[2]; } u;
            memset(&u, 0, sizeof(u))
            u.f80 = node.fval;
            println("  mov $%lu, %%rax  # long double %Lf", u.u64[0], node.fval)
            println("  mov %%rax, -16(%%rsp)")
            println("  mov $%lu, %%rax", u.u64[1])
            println("  mov %%rax, -8(%%rsp)")
            println("  fldt -16(%%rsp)")
*/
            u64lo, u64hi := x64Float80ToBinary(node.fval)
            println("  mov $%u, %%rax  # long double %Lf", u64lo, node.fval)
            println("  mov %%rax, -16(%%rsp)")
            println("  mov $%u, %%rax", u64hi)
            println("  mov %%rax, -8(%%rsp)")
            println("  fldt -16(%%rsp)")
            return
        }

        println("  mov $%d, %%rax", node.val)
        return

    case ND_NEG:
        genExpr(node.lhs)

        switch node.ty.kind {
        case TY_FLOAT:
            println("  mov $1, %%rax")
            println("  shl $31, %%rax")
            println("  movq %%rax, %%xmm1")
            println("  xorps %%xmm1, %%xmm0")
            return
        case TY_DOUBLE:
            println("  mov $1, %%rax")
            println("  shl $63, %%rax")
            println("  movq %%rax, %%xmm1")
            println("  xorpd %%xmm1, %%xmm0")
            return
        case TY_LDOUBLE:
            println("  fchs")
            return
        }

        println("  neg %%rax")
        return
    case ND_VAR:
        genAddr(node)
        load(node.ty)
        return
    case ND_MEMBER:
        genAddr(node)
        load(node.ty)

        mem := node.member
        if mem.isBitfield {
            println("  shl $%d, %%rax", 64-mem.bitWidth-mem.bitOffset)
            if mem.ty.isUnsigned {
                println("  shr $%d, %%rax", 64-mem.bitWidth)
            } else {
                println("  sar $%d, %%rax", 64-mem.bitWidth)
            }
        }
        return
    case ND_DEREF:
        genExpr(node.lhs)
        load(node.ty)
        return
    case ND_ADDR:
        genAddr(node.lhs)
        return
    case ND_ASSIGN:
        genAddr(node.lhs)
        push()
        genExpr(node.rhs)

        if node.lhs.kind == ND_MEMBER && node.lhs.member.isBitfield {
            println("  mov %%rax, %%r8")

            // If the lhs is a bitfield, we need to read the current value
            // from memory and merge it with a new value.
            mem := node.lhs.member
            println("  mov %%rax, %%rdi")
            println("  and $%d, %%rdi", (int64(1)<<mem.bitWidth)-1)
            println("  shl $%d, %%rdi", mem.bitOffset)

            println("  mov (%%rsp), %%rax")
            load(mem.ty)

            mask := ((int64(1) << mem.bitWidth) - 1) << mem.bitOffset
            println("  mov $%d, %%r9", ^mask)
            println("  and %%r9, %%rax")
            println("  or %%rdi, %%rax")
            store(node.ty)
            println("  mov %%r8, %%rax")
            return
        }

        store(node.ty)
        return
    case ND_STMT_EXPR:
        for n := node.body; n != nil; n = n.next {
            genStmt(n)
        }
        return
    case ND_COMMA:
        genExpr(node.lhs)
        genExpr(node.rhs)
        return
    case ND_CAST:
        genExpr(node.lhs)
        genCast(node.lhs.ty, node.ty)
        return
    case ND_MEMZERO:
        // `rep stosb` is equivalent to `memset(%rdi, %al, %rcx)`.
        println("  mov $%d, %%rcx", node.sym.ty.size)
        println("  lea %d(%%rbp), %%rdi", node.sym.offset)
        println("  mov $0, %%al")
        println("  rep stosb")
        return
    case ND_COND:
        c := count()
        genExpr(node.cond)
        cmpZero(node.cond.ty)
        println("  je .L.else.%d", c)
        genExpr(node.then)
        println("  jmp .L.end.%d", c)
        println(".L.else.%d:", c)
        genExpr(node.els)
        println(".L.end.%d:", c)
        return
    case ND_NOT:
        genExpr(node.lhs)
        cmpZero(node.lhs.ty)
        println("  sete %%al")
        println("  movzx %%al, %%rax")
        return
    case ND_BITNOT:
        genExpr(node.lhs)
        println("  not %%rax")
        return
    case ND_LOGAND:
        c := count()
        genExpr(node.lhs)
        cmpZero(node.lhs.ty)
        println("  je .L.false.%d", c)
        genExpr(node.rhs)
        cmpZero(node.rhs.ty)
        println("  je .L.false.%d", c)
        println("  mov $1, %%rax")
        println("  jmp .L.end.%d", c)
        println(".L.false.%d:", c)
        println("  mov $0, %%rax")
        println(".L.end.%d:", c)
        return
    case ND_LOGOR:
        c := count()
        genExpr(node.lhs)
        cmpZero(node.lhs.ty)
        println("  jne .L.true.%d", c)
        genExpr(node.rhs)
        cmpZero(node.rhs.ty)
        println("  jne .L.true.%d", c)
        println("  mov $0, %%rax")
        println("  jmp .L.end.%d", c)
        println(".L.true.%d:", c)
        println("  mov $1, %%rax")
        println(".L.end.%d:", c)
        return
    case ND_FUNCALL:
        if node.lhs.kind == ND_VAR && node.lhs.sym.name == "alloca" {
            genExpr(node.args)
            println("  mov %%rax, %%rdi")
            genBuiltinAlloca()
            return
        }

        stackArgs := pushArgs(node)
        genExpr(node.lhs)

        gp := 0
        fp := 0

        // If the return type is a large struct/union, the caller passes
        // a pointer to a buffer as if it were the first argument.
        if node.retBuffer != nil && node.ty.size > 16 {
            pop(argreg64[gp])
            gp++
        }

        for arg := node.args; arg != nil; arg = arg.next {
            ty := arg.ty;

            switch ty.kind {
            case TY_STRUCT, TY_UNION:
                if ty.size > 16 {
                    continue
                }

                fp1 := 0
                if hasFlonum1(ty) {
                    fp1 = 1
                }
                fp2 := 0
                if hasFlonum2(ty) {
                    fp2 = 1
                }

                if fp + fp1 + fp2 < FP_MAX && gp + (1- fp1) + (1 - fp2) < GP_MAX {
                    if fp1 != 0 {
                        popf(fp)
                        fp++
                    } else {
                        pop(argreg64[gp])
                        gp++
                    }

                    if ty.size > 8 {
                        if fp2 != 0 {
                            popf(fp)
                            fp++
                        } else {
                            pop(argreg64[gp])
                            gp++
                        }
                    }
                }
                // break
            case TY_FLOAT, TY_DOUBLE:
                if fp < FP_MAX {
                    popf(fp)
                    fp++
                }
                // break
            case TY_LDOUBLE:
                // break
            default:
                if gp < GP_MAX {
                    pop(argreg64[gp])
                    gp++
                }
            }
        }

        println("  mov %%rax, %%r10")
        println("  mov $%d, %%rax", fp)
        println("  call *%%r10")
        println("  add $%d, %%rsp", stackArgs*8)

        depth -= stackArgs

        // It looks like the most significant 48 or 56 bits in RAX may
        // contain garbage if a function return type is short or bool/char,
        // respectively. We clear the upper bits here.
        switch node.ty.kind {
        case TY_BOOL:
            println("  movzx %%al, %%eax")
            return
        case TY_CHAR:
            if node.ty.isUnsigned {
                println("  movzbl %%al, %%eax")
            } else {
                println("  movsbl %%al, %%eax")
            }
            return
        case TY_SHORT:
            if node.ty.isUnsigned {
                println("  movzwl %%ax, %%eax")
            } else {
                println("  movswl %%ax, %%eax")
            }
            return
        }

        // If the return type is a small struct, a value is returned
        // using up to two registers.
        if node.retBuffer != nil && node.ty.size <= 16 {
            copyRetBuffer(node.retBuffer)
            println("  lea %d(%%rbp), %%rax", node.retBuffer.offset)
        }

        return
    case ND_LABEL_VAL:
        println("  lea %s(%%rip), %%rax", node.uniqueLabel)
        return
    case ND_CAS:
        genExpr(node.casAddr)
        push()
        genExpr(node.casNew)
        push()
        genExpr(node.casOld)
        println("  mov %%rax, %%r8")
        load(node.casOld.ty.base)
        pop("%rdx") // new
        pop("%rdi") // addr

        sz := node.casAddr.ty.base.size;
        println("  lock cmpxchg %s, (%%rdi)", regDx(sz))
        println("  sete %%cl")
        println("  je 1f")
        println("  mov %s, (%%r8)", regAx(sz))
        println("1:")
        println("  movzbl %%cl, %%eax")
        return
    case ND_EXCH:
        genExpr(node.lhs)
        push()
        genExpr(node.rhs)
        pop("%rdi")

        sz := node.lhs.ty.base.size;
        println("  xchg %s, (%%rdi)", regAx(sz))
        return
    }

    switch node.lhs.ty.kind {
    case TY_FLOAT, TY_DOUBLE:
        genExpr(node.rhs)
        pushf()
        genExpr(node.lhs)
        popf(1)

        var sz string
        if node.lhs.ty.kind == TY_FLOAT {
            sz = "ss"
        } else {
            sz = "sd"
        }

        switch node.kind {
        case ND_ADD:
            println("  add%s %%xmm1, %%xmm0", sz)
            return
        case ND_SUB:
            println("  sub%s %%xmm1, %%xmm0", sz)
            return
        case ND_MUL:
            println("  mul%s %%xmm1, %%xmm0", sz)
            return
        case ND_DIV:
            println("  div%s %%xmm1, %%xmm0", sz)
            return
        case ND_EQ, ND_NE, ND_LT, ND_LE:
            println("  ucomi%s %%xmm0, %%xmm1", sz)

            switch node.kind {
            case ND_EQ:
                println("  sete %%al")
                println("  setnp %%dl")
                println("  and %%dl, %%al")
            case ND_NE:
                println("  setne %%al")
                println("  setp %%dl")
                println("  or %%dl, %%al")
            case ND_LT:
                println("  seta %%al")
            default:
                println("  setae %%al")
            }

            println("  and $1, %%al")
            println("  movzb %%al, %%rax")
            return
        }

        ErrorTok(node.tok, "invalid expression")
    case TY_LDOUBLE:
        genExpr(node.lhs)
        genExpr(node.rhs)

        switch node.kind {
        case ND_ADD:
            println("  faddp")
            return
        case ND_SUB:
            println("  fsubrp")
            return
        case ND_MUL:
            println("  fmulp")
            return
        case ND_DIV:
            println("  fdivrp")
            return
        case ND_EQ, ND_NE, ND_LT, ND_LE:
            println("  fcomip")
            println("  fstp %%st(0)")

            switch node.kind {
            case ND_EQ:
                println("  sete %%al")
            case ND_NE:
                println("  setne %%al")
            case ND_LT:
                println("  seta %%al")
            default:
                println("  setae %%al")
            }

            println("  movzb %%al, %%rax")
            return
        }

        ErrorTok(node.tok, "invalid expression")
    }

    genExpr(node.rhs)
    push()
    genExpr(node.lhs)
    pop("%rdi")

    var ax, di, dx string

    if node.lhs.ty.kind == TY_LONG || node.lhs.ty.base != nil {
        ax = "%rax"
        di = "%rdi"
        dx = "%rdx"
    } else {
        ax = "%eax"
        di = "%edi"
        dx = "%edx"
    }

    switch node.kind {
    case ND_ADD:
        println("  add %s, %s", di, ax)
        return
    case ND_SUB:
        println("  sub %s, %s", di, ax)
        return
    case ND_MUL:
        println("  imul %s, %s", di, ax)
        return
    case ND_DIV, ND_MOD:
        if node.ty.isUnsigned {
            println("  mov $0, %s", dx)
            println("  div %s", di)
        } else {
            if node.lhs.ty.size == 8 {
                println("  cqo")
            } else {
                println("  cdq")
            }
            println("  idiv %s", di)
        }

        if node.kind == ND_MOD {
            println("  mov %%rdx, %%rax")
        }
        return
    case ND_BITAND:
        println("  and %s, %s", di, ax)
        return
    case ND_BITOR:
        println("  or %s, %s", di, ax)
        return
    case ND_BITXOR:
        println("  xor %s, %s", di, ax)
        return
    case ND_EQ, ND_NE, ND_LT, ND_LE:
        println("  cmp %s, %s", di, ax)

        switch node.kind {
        case ND_EQ:
            println("  sete %%al")
        case ND_NE:
            println("  setne %%al")
        case ND_LT:
            if node.lhs.ty.isUnsigned {
                println("  setb %%al")
            } else {
                println("  setl %%al")
            }
        case ND_LE:
            if node.lhs.ty.isUnsigned {
                println("  setbe %%al")
            } else {
                println("  setle %%al")
            }
        }

        println("  movzb %%al, %%rax")
        return
    case ND_SHL:
        println("  mov %%rdi, %%rcx")
        println("  shl %%cl, %s", ax)
        return
    case ND_SHR:
        println("  mov %%rdi, %%rcx")
        if node.lhs.ty.isUnsigned {
            println("  shr %%cl, %s", ax)
        } else {
            println("  sar %%cl, %s", ax)
        }
        return
    }

    ErrorTok(node.tok, "invalid expression")
}

func genStmt(node *Node) { 
    println("  .loc %d %d", node.tok.file.fileNo, node.tok.lineNo)

    switch node.kind {
    case ND_IF:
        c := count()
        genExpr(node.cond)
        cmpZero(node.cond.ty)
        println("  je  .L.else.%d", c)
        genStmt(node.then)
        println("  jmp .L.end.%d", c)
        println(".L.else.%d:", c)
        if node.els != nil {
            genStmt(node.els)
        }
        println(".L.end.%d:", c)
        return
    case ND_FOR:
        c := count()
        if node.init != nil {
            genStmt(node.init)
        }
        println(".L.begin.%d:", c)
        if node.cond != nil {
            genExpr(node.cond)
            cmpZero(node.cond.ty)
            println("  je %s", node.brkLabel)
        }
        genStmt(node.then)
        println("%s:", node.contLabel)
        if node.inc != nil {
            genExpr(node.inc)
        }
        println("  jmp .L.begin.%d", c)
        println("%s:", node.brkLabel)
        return
    case ND_DO:
        c := count()
        println(".L.begin.%d:", c)
        genStmt(node.then)
        println("%s:", node.contLabel)
        genExpr(node.cond)
        cmpZero(node.cond.ty)
        println("  jne .L.begin.%d", c)
        println("%s:", node.brkLabel)
        return
    case ND_SWITCH:
        genExpr(node.cond)

        for n := node.caseNext; n != nil; n = n.caseNext {
            var ax, di string
            if node.cond.ty.size == 8 {
                ax = "%rax"
                di = "%rdi"
            } else {
                ax = "%eax"
                di = "%edi"
            }

            if n.begin == n.end {
                println("  cmp $%d, %s", n.begin, ax)
                println("  je %s", n.label)
                continue;
            }

            // [GNU] Case ranges
            println("  mov %s, %s", ax, di)
            println("  sub $%d, %s", n.begin, di)
            println("  cmp $%d, %s", n.end-n.begin, di)
            println("  jbe %s", n.label)
        }

        if node.defaultCase != nil {
            println("  jmp %s", node.defaultCase.label)
        }

        println("  jmp %s", node.brkLabel)
        genStmt(node.then)
        println("%s:", node.brkLabel)
        return
    case ND_CASE:
        println("%s:", node.label)
        genStmt(node.lhs)
        return
    case ND_BLOCK:
        for n := node.body; n != nil; n = n.next {
            genStmt(n)
        }
        return
    case ND_GOTO:
        println("  jmp %s", node.uniqueLabel)
        return
    case ND_GOTO_EXPR:
        genExpr(node.lhs)
        println("  jmp *%%rax")
        return
    case ND_LABEL:
        println("%s:", node.uniqueLabel)
        genStmt(node.lhs)
        return
    case ND_RETURN:
        if node.lhs != nil {
            genExpr(node.lhs)
            ty := node.lhs.ty

            if ty.kind == TY_STRUCT || ty.kind == TY_UNION {
                if ty.size <= 16 {
                    copyStructReg()
                } else {
                    copyStructMem()
                }
            }
        }

        println("  jmp .L.return.%s", genCurrentFn.name)
        return
    case ND_EXPR_STMT:
        genExpr(node.lhs)
        return
    case ND_ASM:
        println("  %s", node.asmStr)
        return
    }

    ErrorTok(node.tok, "invalid statement")
}

// Assigns offsets to local variables.
func assignLvarOffsets(prog *Obj) {
    for fn := prog; fn != nil; fn = fn.next {
        if !fn.isFunction {
            continue
        }

        // If a function has many parameters, some parameters are
        // inevitably passed by stack rather than by register.
        // The first passed-by-stack parameter resides at RBP+16.
        top := 16
        bottom := 0

        gp := 0
        fp := 0

        // Assign offsets to pass-by-stack parameters.
        for sym := fn.params; sym != nil; sym = sym.next {
            ty := sym.ty

            switch ty.kind {
            case TY_STRUCT, TY_UNION:
                if ty.size <= 16 {
                    fp1 := 0
                    if hasFlonum(ty, 0, 8, 0) {
                        fp1 = 1
                    }
                    fp2 := 0
                    if hasFlonum(ty, 8, 16, 8) {
                        fp2 = 1
                    }
                    if fp + fp1 + fp2 < FP_MAX && gp + (1 - fp1) + (1 - fp2) < GP_MAX {
                        fp = fp + fp1 + fp2
                        gp = gp + (1 - fp1) + (1 - fp2)
                        continue
                    }
                }
                // break
            case TY_FLOAT, TY_DOUBLE:
                if fp < FP_MAX {
                    fp++
                    continue
                }
                fp++
                // break
            case TY_LDOUBLE:
                // break
            default:
                if gp < GP_MAX {
                    gp++
                    continue
                }
                gp++
            }

            top = AlignTo(top, 8)
            sym.offset = top
            top += sym.ty.size
        }

        // Assign offsets to pass-by-register parameters and local variables.
        for sym := fn.locals; sym != nil; sym = sym.next {
            if sym.offset != 0 {
                continue
            }

            // AMD64 System V ABI has a special alignment rule for an array of
            // length at least 16 bytes. We need to align such array to at least
            // 16-byte boundaries. See p.14 of
            // https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-draft.pdf.
            var align int
            if sym.ty.kind == TY_ARRAY && sym.ty.size >= 16 {
                align = IntMax(16, sym.align)
            } else {
                align = sym.align
            }

            bottom += sym.ty.size;
            bottom = AlignTo(bottom, align)
            sym.offset = -bottom;
        }

        fn.stackSize = AlignTo(bottom, 16)
    }
}

func emitData(prog *Obj) {
    for sym := prog; sym != nil; sym = sym.next {
        if sym.isFunction || !sym.isDefinition {
            continue
        }

        if sym.isStatic {
            println("  .local %s", sym.name)
        } else {
            println("  .globl %s", sym.name)
        }

        var align int
        if sym.ty.kind == TY_ARRAY && sym.ty.size >= 16 {
            align = IntMax(16, sym.align)
        } else {
            align = sym.align
        }


        // Common symbol
        if optFcommon && sym.isTentative {
            println("  .comm %s, %d, %d", sym.name, sym.ty.size, align)
            continue
        }

        // .data or .tdata
        if sym.initData != nil {
            if sym.isTls {
                println("  .section .tdata,\"awT\",@progbits")
            } else {
                println("  .data")
            }

            println("  .type %s, @object", sym.name)
            println("  .size %s, %d", sym.name, sym.ty.size)
            println("  .align %d", align)
            println("%s:", sym.name)

            rel := sym.rel
            pos := 0
            for pos < sym.ty.size {
                if rel != nil && rel.offset == pos {
                    println("  .quad %s%+ld", *rel.label, rel.addend)
                    rel = rel.next
                    pos += 8
                } else {
                    println("  .byte %d", sym.initData[pos])
                    pos++
                }
            }
            continue
        }

        // .bss or .tbss
        if sym.isTls {
            println("  .section .tbss,\"awT\",@nobits")
        } else {
            println("  .bss")
        }

        println("  .align %d", align)
        println("%s:", sym.name)
        println("  .zero %d", sym.ty.size)
    }
}

func storeFp(r int, offset int, sz int) {
    switch sz {
    case 4:
        println("  movss %%xmm%d, %d(%%rbp)", r, offset)
        return
    case 8:
        println("  movsd %%xmm%d, %d(%%rbp)", r, offset)
        return
    }
    Unreachable()
}

func storeGp(r int, offset int, sz int) {
    switch sz {
    case 1:
        println("  mov %s, %d(%%rbp)", argreg8[r], offset)
        return
    case 2:
        println("  mov %s, %d(%%rbp)", argreg16[r], offset)
        return
    case 4:
        println("  mov %s, %d(%%rbp)", argreg32[r], offset)
        return
    case 8:
        println("  mov %s, %d(%%rbp)", argreg64[r], offset)
        return
    default:
        for i := 0; i < sz; i++ {
            println("  mov %s, %d(%%rbp)", argreg8[r], offset+i)
            println("  shr $8, %s", argreg64[r])
        }
        return
    }
} 

func emitText(prog *Obj) {
    for fn := prog; fn != nil; fn = fn.next {
        if !fn.isFunction || !fn.isDefinition {
            continue
        }

        // No code is emitted for "static inline" functions
        // if no one is referencing them.
        if !fn.isLive {
            continue
        }

        if fn.isStatic {
            println("  .local %s", fn.name)
        } else {
            println("  .globl %s", fn.name)
        }

        println("  .text")
        println("  .type %s, @function", fn.name)
        println("%s:", fn.name)
        genCurrentFn = fn

        // Prologue
        println("  push %%rbp")
        println("  mov %%rsp, %%rbp")
        println("  sub $%d, %%rsp", fn.stackSize)
        println("  mov %%rsp, %d(%%rbp)", fn.allocaBottom.offset)

        // Save arg registers if function is variadic
        if fn.vaArea != nil{
            gp := 0
            fp := 0
            for sym := fn.params; sym != nil; sym = sym.next {
                if IsFlonum(sym.ty) {
                    fp++
                } else {
                    gp++
                }
            }

            off := fn.vaArea.offset

            // va_elem
            println("  movl $%d, %d(%%rbp)", gp*8, off)      // gp_offset
            println("  movl $%d, %d(%%rbp)", fp*8+48, off+4) // fp_offset
            println("  movq %%rbp, %d(%%rbp)", off+8)        // overflow_arg_area
            println("  addq $16, %d(%%rbp)", off+8)
            println("  movq %%rbp, %d(%%rbp)", off+16)       // reg_save_area
            println("  addq $%d, %d(%%rbp)", off+24, off+16)

            // __reg_save_area__
            println("  movq %%rdi, %d(%%rbp)", off+24)
            println("  movq %%rsi, %d(%%rbp)", off+32)
            println("  movq %%rdx, %d(%%rbp)", off+40)
            println("  movq %%rcx, %d(%%rbp)", off+48)
            println("  movq %%r8, %d(%%rbp)", off+56)
            println("  movq %%r9, %d(%%rbp)", off+64)
            println("  movsd %%xmm0, %d(%%rbp)", off+72)
            println("  movsd %%xmm1, %d(%%rbp)", off+80)
            println("  movsd %%xmm2, %d(%%rbp)", off+88)
            println("  movsd %%xmm3, %d(%%rbp)", off+96)
            println("  movsd %%xmm4, %d(%%rbp)", off+104)
            println("  movsd %%xmm5, %d(%%rbp)", off+112)
            println("  movsd %%xmm6, %d(%%rbp)", off+120)
            println("  movsd %%xmm7, %d(%%rbp)", off+128)
        }

        // Save passed-by-register arguments to the stack
        gp := 0
        fp := 0
        for sym := fn.params; sym != nil; sym = sym.next {
            if sym.offset > 0 {
                continue
            }

            ty := sym.ty

            switch ty.kind {
            case TY_STRUCT, TY_UNION:
                Assert(ty.size <= 16)
                if hasFlonum(ty, 0, 8, 0) {
                    storeFp(fp, sym.offset, IntMin(8, ty.size))
                    fp++
                } else {
                    storeGp(gp, sym.offset, IntMin(8, ty.size))
                    gp++
                }

                if ty.size > 8 {
                    if hasFlonum(ty, 8, 16, 0) {
                        storeFp(fp, sym.offset+8, ty.size-8)
                        fp++
                    } else {
                        storeGp(gp, sym.offset+8, ty.size-8)
                        gp++
                    }
                }
                // break
            case TY_FLOAT, TY_DOUBLE:
                storeFp(fp, sym.offset, ty.size)
                fp++
                // break
            default:
                storeGp(gp, sym.offset, ty.size)
                gp++
            }
        }

        // Emit code
        genStmt(fn.body)
        Assert(depth == 0)

        // [https://www.sigbus.info/n1570#5.1.2.2.3p1] The C spec defines
        // a special rule for the main function. Reaching the end of the
        // main function is equivalent to returning 0, even though the
        // behavior is undefined for the other functions.
        if fn.name == "main" {
            println("  mov $0, %%rax")
        }

        // Epilogue
        println(".L.return.%s:", fn.name)
        println("  mov %%rbp, %%rsp")
        println("  pop %%rbp")
        println("  ret")
    }
}

func x64Float32ToBinary(val float64) uint32 {
    // TODO
    return 0
}

func x64Float64ToBinary(val float64) uint64 {
    // TODO
    return 0
}

func x64Float80ToBinary(val float64) (uint64, uint64) {
    // float80 is not supported
    return x64Float64ToBinary(val), 0
}

//
//    Public functions
//

func Codegen(prog *Obj, out io.Writer, opt *Options) {
    InitCodegen(opt)

    outputFile = out

    files := GetInputFiles()
    for _, file := range files {
        println("  .file %d \"%s\"", file.fileNo, file.name)
    }

    assignLvarOffsets(prog)
    emitData(prog)
    emitText(prog)
}

