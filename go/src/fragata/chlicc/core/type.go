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

//
//    TypeKind
//

type TypeKind int

const (
    TY_VOID TypeKind = iota
    TY_BOOL
    TY_CHAR
    TY_SHORT
    TY_INT
    TY_LONG
    TY_FLOAT
    TY_DOUBLE
    TY_LDOUBLE
    TY_ENUM
    TY_PTR
    TY_FUNC
    TY_ARRAY
    TY_VLA // variable-length array
    TY_STRUCT
    TY_UNION
)

//
//    Type
//

type Type struct {
    kind TypeKind
    size int           // sizeof() value
    align int          // alignment
    isUnsigned bool   // unsigned or signed
    isAtomic bool     // true if _Atomic
    origin *Type       // for type compatibility check

    // Pointer-to or array-of type. We intentionally use the same member
    // to represent pointer/array duality in C.
    //
    // In many contexts in which a pointer is expected, we examine this
    // member instead of "kind" member to determine whether a type is a
    // pointer or not. That means in many contexts "array of T" is
    // naturally handled as if it were "pointer to T", as required by
    // the C spec.
    base *Type

    // Declaration
    name *Token
    namePos *Token

    // Array
    arrayLen int

    // Variable-length array
    vlaLen *Node // # of elements
    vlaSize *Obj // sizeof() value

    // Struct
    members *Member
    isFlexible bool
    isPacked bool

    // Function type
    returnTy *Type
    params *Type
    isVariadic bool
    next *Type
}

//
//    Member
//

type Member struct {
    next *Member
    ty *Type
    tok *Token // for error message
    name *Token
    idx int
    align int
    offset int

    // Bitfield
    isBitfield bool
    bitOffset int
    bitWidth int
}

//
//    Immutable public variables
//

var (
    TyVoid = &Type{kind: TY_VOID, size: 1, align: 1}
    TyBool = &Type{kind: TY_BOOL, size: 1, align: 1}

    TyChar = &Type{kind: TY_CHAR, size: 1, align: 1}
    TyShort = &Type{kind: TY_SHORT, size: 2, align: 2}
    TyInt = &Type{kind: TY_INT, size: 4, align: 4}
    TyLong = &Type{kind: TY_LONG, size: 8, align: 8}

    TyUchar = &Type{kind: TY_CHAR, size: 1, align: 1, isUnsigned: true}
    TyUshort = &Type{kind: TY_SHORT, size: 2, align: 2, isUnsigned: true}
    TyUint = &Type{kind: TY_INT, size: 4, align: 4, isUnsigned: true}
    TyUlong = &Type{kind: TY_LONG, size: 8, align: 8, isUnsigned: true}

    TyFloat = &Type{kind: TY_FLOAT, size: 4, align: 4}
    TyDouble = &Type{kind: TY_DOUBLE, size: 8, align: 8}
    TyLdouble = &Type{kind: TY_LDOUBLE, size: 16, align: 16}
)

//
//    Private functions
//

func newType(kind TypeKind, size int, align int) *Type {
    ty := new(Type)
    ty.kind = kind
    ty.size = size
    ty.align = align
    return ty
}

//
//    Pubic functions
//

func IsInteger(ty *Type) bool {
    k := ty.kind
    return (k == TY_BOOL || k == TY_CHAR || k == TY_SHORT ||
        k == TY_INT  || k == TY_LONG || k == TY_ENUM)
}

func IsFlonum(ty *Type) bool {
    k := ty.kind
    return (k == TY_FLOAT || k == TY_DOUBLE || k == TY_LDOUBLE)
}

func IsNumeric(ty *Type) bool {
  return (IsInteger(ty) || IsFlonum(ty))
}

func IsCompatible(t1 *Type, t2 *Type) bool {
    if t1 == t2 {
        return true
    }

    if t1.origin != nil {
        return IsCompatible(t1.origin, t2)
    }

    if t2.origin != nil {
        return IsCompatible(t1, t2.origin)
    }

    if t1.kind != t2.kind {
        return false
    }

    switch t1.kind {
    case TY_CHAR, TY_SHORT, TY_INT, TY_LONG:
        return (t1.isUnsigned == t2.isUnsigned)
    case TY_FLOAT, TY_DOUBLE, TY_LDOUBLE:
        return true
    case TY_PTR:
        return IsCompatible(t1.base, t2.base)
    case TY_FUNC:
        if !IsCompatible(t1.returnTy, t2.returnTy) {
            return false
        }
        if t1.isVariadic != t2.isVariadic {
            return false
        }
        p1 := t1.params
        p2 := t2.params
        for p1 != nil && p2 != nil {
            if !IsCompatible(p1, p2) {
                return false
            }
            p1 = p1.next
            p2 = p2.next
        }
        return (p1 == nil && p2 == nil)
    case TY_ARRAY:
        if !IsCompatible(t1.base, t2.base) {
            return false
        }
        return (t1.arrayLen < 0 && t2.arrayLen < 0 && t1.arrayLen == t2.arrayLen)
    }
    return false
}

func CopyType(ty *Type) *Type {
    ret := new(Type)
    *ret = *ty
    ret.origin = ty
    return ret
} 

func PointerTo(base *Type) *Type {
    ty := newType(TY_PTR, 8, 8)
    ty.base = base
    ty.isUnsigned = true
    return ty
}

func FuncType(returnTy *Type) *Type {
    // The C spec disallows sizeof(<function type>), but
    // GCC allows that and the expression is evaluated to 1.
    ty := newType(TY_FUNC, 1, 1)
    ty.returnTy = returnTy
    return ty
} 

func ArrayOf(base *Type, n int) *Type {
    ty := newType(TY_ARRAY, base.size*n, base.align)
    ty.base = base
    ty.arrayLen = n
    return ty
}

func VlaOf(base *Type, n *Node) *Type {
    ty := newType(TY_VLA, 8, 8)
    ty.base = base
    ty.vlaLen = n
    return ty
}

func EnumType() *Type {
    return newType(TY_ENUM, 4, 4)
}

func StructType() *Type {
    return newType(TY_STRUCT, 0, 1)
} 

func getCommonType(ty1 *Type, ty2 *Type) *Type {
    if ty1.base != nil {
        return PointerTo(ty1.base)
    }

    if ty1.kind == TY_FUNC {
        return PointerTo(ty1)
    }
    if ty2.kind == TY_FUNC {
        return PointerTo(ty2)
    }

    if ty1.kind == TY_LDOUBLE || ty2.kind == TY_LDOUBLE {
        return TyLdouble
    }
    if ty1.kind == TY_DOUBLE || ty2.kind == TY_DOUBLE {
        return TyDouble
    }
    if ty1.kind == TY_FLOAT || ty2.kind == TY_FLOAT {
        return TyFloat
    }

    if ty1.size < 4 {
        ty1 = TyInt
    }
    if ty2.size < 4 {
        ty2 = TyInt
    }

    if ty1.size < ty2.size {
        return ty2
    }
    if ty1.size > ty2.size {
        return ty1
    }

    if ty2.isUnsigned {
        return ty2
    }
    return ty1
}

// For many binary operators, we implicitly promote operands so that
// both operands have the same type. Any integral type smaller than
// int is always promoted to int. If the type of one operand is larger
// than the other's (e.g. "long" vs. "int"), the smaller operand will
// be promoted to match with the other.
//
// This operation is called the "usual arithmetic conversion".
func usualArithConv(lhs *Node, rhs *Node) (*Node, *Node) {
    ty := getCommonType(lhs.ty, rhs.ty)
    lhs = NewCast(lhs, ty)
    rhs = NewCast(rhs, ty)
    return lhs, rhs
}

func AddType(node *Node) {
    if node == nil || node.ty != nil {
        return
    }

    AddType(node.lhs)
    AddType(node.rhs)
    AddType(node.cond)
    AddType(node.then)
    AddType(node.els)
    AddType(node.init)
    AddType(node.inc)

    for n := node.body; n != nil; n = n.next {
        AddType(n)
    }
    for n := node.args; n != nil; n = n.next {
        AddType(n)
    }

    switch node.kind {
    case ND_NUM:
        node.ty = TyInt
        return
    case ND_ADD, ND_SUB, ND_MUL, ND_DIV, ND_MOD, ND_BITAND, ND_BITOR, ND_BITXOR:
        node.lhs, node.rhs = usualArithConv(node.lhs, node.rhs)
        node.ty = node.lhs.ty
        return
    case ND_NEG:
        ty := getCommonType(TyInt, node.lhs.ty)
        node.lhs = NewCast(node.lhs, ty)
        node.ty = ty
        return
    case ND_ASSIGN:
        if node.lhs.ty.kind == TY_ARRAY {
            ErrorTok(node.lhs.tok, "not an lvalue")
        }
        if node.lhs.ty.kind != TY_STRUCT {
            node.rhs = NewCast(node.rhs, node.lhs.ty)
        }
        node.ty = node.lhs.ty
        return
    case ND_EQ, ND_NE, ND_LT, ND_LE:
        node.lhs, node.rhs = usualArithConv(node.lhs, node.rhs)
        node.ty = TyInt
        return
    case ND_FUNCALL:
        node.ty = node.funcTy.returnTy
        return
    case ND_NOT, ND_LOGOR, ND_LOGAND:
        node.ty = TyInt
        return
    case ND_BITNOT, ND_SHL, ND_SHR:
        node.ty = node.lhs.ty
        return
    case ND_VAR, ND_VLA_PTR:
        node.ty = node.sym.ty
        return
    case ND_COND:
        if node.then.ty.kind == TY_VOID || node.els.ty.kind == TY_VOID {
            node.ty = TyVoid
        } else {
            node.then, node.els = usualArithConv(node.then, node.els)
            node.ty = node.then.ty
        }
        return
    case ND_COMMA:
        node.ty = node.rhs.ty
        return
    case ND_MEMBER:
        node.ty = node.member.ty
        return
    case ND_ADDR:
        ty := node.lhs.ty
        if ty.kind == TY_ARRAY {
            node.ty = PointerTo(ty.base)
        } else {
            node.ty = PointerTo(ty)
        }
        return
    case ND_DEREF:
        if node.lhs.ty.base == nil {
            ErrorTok(node.tok, "invalid pointer dereference")
        }
        if node.lhs.ty.base.kind == TY_VOID {
            ErrorTok(node.tok, "dereferencing a void pointer")
        }
        node.ty = node.lhs.ty.base
        return
    case ND_STMT_EXPR:
        if node.body != nil {
            stmt := node.body
            for stmt.next != nil {
                stmt = stmt.next
            }
            if stmt.kind == ND_EXPR_STMT {
                node.ty = stmt.lhs.ty
                return
            }
        }
        ErrorTok(node.tok, "statement expression returning void is not supported")
        return
    case ND_LABEL_VAL:
        node.ty = PointerTo(TyVoid)
        return
    case ND_CAS:
        AddType(node.casAddr)
        AddType(node.casOld)
        AddType(node.casNew)
        node.ty = TyBool
        if node.casAddr.ty.kind != TY_PTR {
            ErrorTok(node.casAddr.tok, "pointer expected")
        }
        if node.casOld.ty.kind != TY_PTR {
            ErrorTok(node.casOld.tok, "pointer expected")
        }
        return
    case ND_EXCH:
        if node.lhs.ty.kind != TY_PTR {
            ErrorTok(node.casAddr.tok, "pointer expected")
        }
        node.ty = node.lhs.ty.base
        return
    }
}

