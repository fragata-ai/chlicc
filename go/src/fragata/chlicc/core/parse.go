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

import "fmt"

//
//    Obj
//

// variable or function
type Obj struct {
    next *Obj
    name string  // Variable name
    ty *Type     // Type
    tok *Token   // representative token
    isLocal bool // local or global/function
    align int    // alignment

    // Local variable
    offset int

    // Global variable or function
    isFunction bool
    isDefinition bool
    isStatic bool

    // Global variable
    isTentative bool
    isTls bool
    initData []byte
    rel *Relocation

    // Function
    isInline bool
    params *Obj
    body *Node
    locals *Obj
    vaArea *Obj
    allocaBottom *Obj
    stackSize int

    // Static inline function
    isLive bool
    isRoot bool
    refs []string
}

//
//    Relocation
//

// Global variable can be initialized either by a constant expression
// or a pointer to another global variable. This struct represents the
// latter.
type Relocation struct {
    next *Relocation
    offset int
    label *string
    addend int64
}

//
//    NodeKind
//

// AST node type
type NodeKind int

const (
    ND_NULL_EXPR NodeKind = iota // Do nothing
    ND_ADD                       // +
    ND_SUB                       // -
    ND_MUL                       // *
    ND_DIV                       // /
    ND_NEG                       // unary -
    ND_MOD                       // %
    ND_BITAND                    // &
    ND_BITOR                     // |
    ND_BITXOR                    // ^
    ND_SHL                       // <<
    ND_SHR                       // >>
    ND_EQ                        // ==
    ND_NE                        // !=
    ND_LT                        // <
    ND_LE                        // <=
    ND_ASSIGN                    // =
    ND_COND                      // ?:
    ND_COMMA                     //                 
    ND_MEMBER                    // . (struct member access)
    ND_ADDR                      // unary &
    ND_DEREF                     // unary *
    ND_NOT                       // !
    ND_BITNOT                    // ~
    ND_LOGAND                    // &&
    ND_LOGOR                     // ||
    ND_RETURN                    // "return"
    ND_IF                        // "if"
    ND_FOR                       // "for" or "while"
    ND_DO                        // "do"
    ND_SWITCH                    // "switch"
    ND_CASE                      // "case"
    ND_BLOCK                     // { ... }
    ND_GOTO                      // "goto"
    ND_GOTO_EXPR                 // "goto" labels-as-values
    ND_LABEL                     // Labeled statement
    ND_LABEL_VAL                 // [GNU] Labels-as-values
    ND_FUNCALL                   // Function call
    ND_EXPR_STMT                 // Expression statement
    ND_STMT_EXPR                 // Statement expression
    ND_VAR                       // Variable
    ND_VLA_PTR                   // VLA designator
    ND_NUM                       // Integer
    ND_CAST                      // Type cast
    ND_MEMZERO                   // Zero-clear a stack variable
    ND_ASM                       // "asm"
    ND_CAS                       // Atomic compare-and-swap
    ND_EXCH                      // Atomic exchange
)

//
//    Node
//

// AST node
type Node struct {
    kind NodeKind // Node kind
    next *Node    // Next node
    ty *Type      // Type, e.g. int or pointer to int
    tok *Token    // Representative token

    lhs *Node     // Left-hand side
    rhs *Node     // Right-hand side

    // "if" or "for" statement
    cond *Node
    then *Node
    els *Node
    init *Node
    inc *Node

    // "break" and "continue" labels
    brkLabel string
    contLabel string

    // Block or statement expression
    body *Node

    // Struct member access
    member *Member

    // Function call
    funcTy *Type
    args *Node
    passByStack bool
    retBuffer *Obj

    // Goto or labeled statement, or labels-as-values
    label string
    uniqueLabel string
    gotoNext *Node

    // Switch
    caseNext *Node
    defaultCase *Node

    // Case
    begin int64
    end int64

    // "asm" string literal
    asmStr string

    // Atomic compare-and-swap
    casAddr *Node
    casOld *Node
    casNew *Node

    // Atomic op= operators
    atomicAddr *Obj
    atomicExpr *Node

    // Variable
    varObj *Obj

    // Numeric literal
    val int64
    fval float64
}

//
//    Private types
//

//
//    VarScope
//

// Scope for local variables, global variables, typedefs
// or enum constants
type VarScope struct {
    varObj *Obj
    typeDef *Type
    enumTy *Type
    enumVal int
}

//
//    Scope
//

// Represents a block scope.
type Scope struct {
    next *Scope

    // C has two block scopes; one is for variables/typedefs and
    // the other is for struct/union/enum tags.
    vars map[string]*VarScope
    tags map[string]*Type
}

//
//    VarAttr
//

// Variable attributes such as typedef or extern.
type VarAttr struct {
    isTypedef bool
    isStatic bool
    isExtern bool
    isInline bool
    isTls bool
    align int
}

//
//    Initializer
//

// This struct represents a variable initializer. Since initializers
// can be nested (e.g. `int x[2][2] = {{1, 2}, {3, 4}}`), this struct
// is a tree data structure.
type Initializer struct {
    next *Initializer
    ty *Type
    tok *Token
    isFlexible bool

    // If it's not an aggregate type and has an initializer,
    // `expr` has an initialization expression.
    expr *Node

    // If it's an initializer for an aggregate type (e.g. array or struct),
    // `children` has initializers for its children.
    children []*Initializer

    // Only one member can be initialized for a union.
    // `mem` is used to clarify which member is initialized.
    mem *Member
}

//
//    InitDesg
//

// For local variable initializer.
type InitDesg struct {
    next *InitDesg
    idx int
    member *Member
    varObj *Obj
}

//
//    Private state variables
//

var (
    // All local variable instances created during parsing are
    // accumulated to this list.
    locals *Obj

    // Likewise, global variables are accumulated to this list.
    globals *Obj

    scope *Scope

    // Points to the function object the parser is currently parsing.
    currentFn *Obj

    // Lists of all goto statements and labels in the curent function.
    gotos *Node
    labels *Node

    // Current "goto" and "continue" jump targets.
    brkLabel string
    contLabel string

    // Points to a node representing a switch if we are parsing
    // a switch statement. Otherwise, nil.
    currentSwitch *Node

    builtinAlloca *Obj

    uniqueNameNextId int
)

func init() {
    locals = nil
    globals = nil
    scope = newScope()
    currentFn = nil
    gotos = nil
    labels = nil
    brkLabel = ""
    contLabel = ""
    currentSwitch = nil
    builtinAlloca = nil
    uniqueNameNextId = 0
}

//
//    Functions
//

// NOTE: Originally defined in 'codegen.c'

// Rounds up `n` to the nearest multiple of `align`. For instance,
// AlignTo(5, 8) returns 8 and AlignTo(11, 8) returns 16.
func AlignTo(n int, align int) int {
    return (n + align - 1) / align * align
}

func alignDown(n int, align int) int {
    return AlignTo(n-align+1, align)
}

func newScope() *Scope {
    sc := new(Scope)
    sc.vars = make(map[string]*VarScope)
    sc.tags = make(map[string]*Type)
    return sc
}

func enterScope() {
    sc := newScope()
    sc.next = scope
    scope = sc
}

func leaveScope() {
    scope = scope.next
}

// Find a variable by name.
func findVar(tok *Token) *VarScope {
    text := string(tok.text)
    for sc := scope; sc != nil; sc = sc.next {
        sc2, ok := sc.vars[text]
        if ok {
            return sc2
        }
    }
    return nil
}

func findTag(tok *Token) *Type {
    text := string(tok.text)
    for sc := scope; sc != nil; sc = sc.next {
        ty, ok := sc.tags[text]
        if ok {
            return ty
        }
    }
    return nil
}

func newNode(kind NodeKind, tok *Token) *Node {
    node := new(Node)
    node.kind = kind
    node.tok = tok
    return node
}

func newBinary(kind NodeKind, lhs *Node, rhs *Node, tok *Token) *Node {
    node := newNode(kind, tok)
    node.lhs = lhs
    node.rhs = rhs
    return node
}

func newUnary(kind NodeKind, expr *Node, tok *Token) *Node {
    node := newNode(kind, tok)
    node.lhs = expr
    return node
}

func newNum(val int64, tok *Token) *Node {
    node := newNode(ND_NUM, tok)
    node.val = val
    return node
}

func newLong(val int64, tok *Token) *Node {
    node := newNode(ND_NUM, tok)
    node.val = val
    node.ty = TyLong
    return node
}

func newUlong(val int64, tok *Token) *Node {
    node := newNode(ND_NUM, tok)
    node.val = val
    node.ty = TyUlong
    return node
}

func newVarNode(varObj *Obj, tok *Token) *Node {
    node := newNode(ND_VAR, tok)
    node.varObj = varObj
    return node
}

func newVlaPtr(varObj *Obj, tok *Token) *Node {
    node := newNode(ND_VLA_PTR, tok)
    node.varObj = varObj
    return node
}

func NewCast(expr *Node, ty *Type) *Node {
    AddType(expr)
    node := new(Node)
    node.kind = ND_CAST
    node.tok = expr.tok
    node.lhs = expr
    node.ty = CopyType(ty)
    return node
}

func pushScope(name string) *VarScope {
    sc := new(VarScope)
    scope.vars[name] = sc
    return sc
}

func newInitializer(ty *Type, isFlexible bool) *Initializer {
    init := new(Initializer)
    init.ty = ty

    if ty.kind == TY_ARRAY {
        if isFlexible && ty.size < 0 {
            init.isFlexible = true
            return init
        }

        init.children = make([]*Initializer, ty.arrayLen)
        for i := 0; i < ty.arrayLen; i++ {
            init.children[i] = newInitializer(ty.base, false)
        }
        return init
    }

    if ty.kind == TY_STRUCT || ty.kind == TY_UNION {
        // Count the number of struct members.
        n := 0
        for mem := ty.members; mem != nil; mem = mem.next {
            n++
        }

        init.children = make([]*Initializer, n)

        for mem := ty.members; mem != nil; mem = mem.next {
            if isFlexible && ty.isFlexible && mem.next == nil {
                child := new(Initializer)
                child.ty = mem.ty
                child.isFlexible = true
                init.children[mem.idx] = child
            } else {
                init.children[mem.idx] = newInitializer(mem.ty, false)
            }
        }
        return init
    }

    return init
}

func newVar(name string, ty *Type) *Obj {
    obj := new(Obj)
    obj.name = name
    obj.ty = ty
    obj.align = ty.align
    pushScope(name).varObj = obj
    return obj
}

func newLvar(name string, ty *Type) *Obj {
    obj := newVar(name, ty)
    obj.isLocal = true
    obj.next = locals
    locals = obj
    return obj
}

func newGvar(name string, ty *Type) *Obj {
    obj := newVar(name, ty)
    obj.next = globals
    obj.isStatic = true
    obj.isDefinition = true
    globals = obj
    return obj
}

func newUniqueName() string {
    id := uniqueNameNextId
    uniqueNameNextId++
    return fmt.Sprintf(".L..%d", id)
}

func newAnonGvar(ty *Type) *Obj {
    return newGvar(newUniqueName(), ty)
}

func newStringLiteral(p []byte, ty *Type) *Obj {
    obj := newAnonGvar(ty)
    obj.initData = p
    return obj
}

func getIdent(tok *Token) string {
    if tok.kind != TK_IDENT {
        ErrorTok(tok, "expected an identifier")
    }
    return string(tok.text)
}

func findTypedef(tok *Token) *Type {
    if tok.kind == TK_IDENT {
        sc := findVar(tok)
        if sc != nil {
            return sc.typeDef
        }
    }
    return nil
}

func pushTagScope(tok *Token, ty *Type) {
    scope.tags[string(tok.text)] = ty
}

// declspec = ("void" | "_Bool" | "char" | "short" | "int" | "long"
//             | "typedef" | "static" | "extern" | "inline"
//             | "_Thread_local" | "__thread"
//             | "signed" | "unsigned"
//             | struct-decl | union-decl | typedef-name
//             | enum-specifier | typeof-specifier
//             | "const" | "volatile" | "auto" | "register" | "restrict"
//             | "__restrict" | "__restrict__" | "_Noreturn")+
//
// The order of typenames in a type-specifier doesn't matter. For
// example, `int long static` means the same as `static long int`.
// That can also be written as `static long` because you can omit
// `int` if `long` or `short` are specified. However, something like
// `char int` is not a valid type specifier. We have to accept only a
// limited combinations of the typenames.
//
// In this function, we count the number of occurrences of each typename
// while keeping the "current" type object that the typenames up
// until that point represent. When we reach a non-typename token,
// we returns the current type object.
func declspec(tok *Token, attr *VarAttr) (rest *Token, out *Type) {
    // We use a single integer as counters for all typenames.
    // For example, bits 0 and 1 represents how many times we saw the
    // keyword "void" so far. With this, we can use a switch statement
    // as you can see below.
    const (
        VOID     = 1 << 0
        BOOL     = 1 << 2
        CHAR     = 1 << 4
        SHORT    = 1 << 6
        INT      = 1 << 8
        LONG     = 1 << 10
        FLOAT    = 1 << 12
        DOUBLE   = 1 << 14
        OTHER    = 1 << 16
        SIGNED   = 1 << 17
        UNSIGNED = 1 << 18
    )

    ty := TyInt
    counter := 0
    isAtomic := false

    for isTypename(tok) {
        // Handle storage class specifiers.
        if EqualAny(tok, 
                "typedef", "static", "extern", 
                "inline", "_Thread_local", "__thread") {
            if attr == nil {
                ErrorTok(tok, "storage class specifier is not allowed in this context")
            }

            switch {
            case Equal(tok, "typedef"):
                attr.isTypedef = true
            case Equal(tok, "static"):
                attr.isStatic = true
            case Equal(tok, "extern"):
                attr.isExtern = true
            case Equal(tok, "inline"):
                attr.isInline = true
            default:
                attr.isTls = true
            }

            // TODO: Check the original code (why sum > 1 there?)
            if attr.isTypedef &&
                    (attr.isStatic || attr.isExtern || attr.isInline || attr.isTls) {
                ErrorTok(tok, 
                    "typedef may not be used together with static,"+
                    " extern, inline, __thread or _Thread_local")
            }
            tok = tok.next
            continue
        }

        // These keywords are recognized but ignored.
        var ignore bool
        tok, ignore = 
            ConsumeAny(tok, 
                "const", "volatile", "auto", "register", 
                "restrict", "__restrict", "__restrict__", "_Noreturn")
        if ignore {
            continue
        }

        if Equal(tok, "_Atomic") {
            tok = tok.next
            if Equal(tok , "(") {
                tok, ty = typename(tok.next)
                tok = Skip(tok, ")")
            }
            isAtomic = true
            continue
        }

        if Equal(tok, "_Alignas") {
            if attr == nil {
                ErrorTok(tok, "_Alignas is not allowed in this context")
            }
            tok = Skip(tok.next, "(")
            if isTypename(tok) {
                var ty2 *Type
                tok, ty2 = typename(tok)
                attr.align = ty2.align
            } else {
                var val int64
                tok, val = ConstExpr(tok)
                attr.align = int(val)
            }
            tok = Skip(tok, ")")
            continue
        }

        // Handle user-defined types.
        ty2 := findTypedef(tok)
        if ty2 != nil || EqualAny(tok, "struct", "union", "enum", "typeof") {
            if counter != 0 {
                break
            }
            switch {
            case Equal(tok, "struct"):
                tok, ty = structDecl(tok.next)
            case Equal(tok, "union"):
                tok, ty = unionDecl(tok.next)
            case Equal(tok, "enum"):
                tok, ty = enumSpecifier(tok.next)
            case Equal(tok, "typeof"):
                tok, ty = typeofSpecifier(tok.next)
            default:
                ty = ty2
                tok = tok.next
            }
            counter += OTHER
            continue
        }

        // Handle built-in types.
        switch {
        case Equal(tok, "void"):
            counter += VOID
        case Equal(tok, "_Bool"):
            counter += BOOL
        case Equal(tok, "char"):
            counter += CHAR
        case Equal(tok, "short"):
            counter += SHORT
        case Equal(tok, "int"):
            counter += INT
        case Equal(tok, "long"):
            counter += LONG
        case Equal(tok, "float"):
            counter += FLOAT
        case Equal(tok, "double"):
            counter += DOUBLE
        case Equal(tok, "signed"):
            counter |= SIGNED
        case Equal(tok, "unsigned"):
            counter |= UNSIGNED
        default:
            Unreachable()
        }

        switch counter {
        case VOID:
            ty = TyVoid
        case BOOL:
            ty = TyBool
        case CHAR, SIGNED + CHAR:
            ty = TyChar
        case UNSIGNED + CHAR:
            ty = TyUchar
        case SHORT, SHORT + INT, SIGNED + SHORT, SIGNED + SHORT + INT:
            ty = TyShort
        case UNSIGNED + SHORT, UNSIGNED + SHORT + INT:
            ty = TyUshort
        case INT, SIGNED, SIGNED + INT:
            ty = TyInt
        case UNSIGNED, UNSIGNED + INT:
            ty = TyUint
        case LONG, LONG + INT, 
                LONG + LONG, LONG + LONG + INT,
                SIGNED + LONG, SIGNED + LONG + INT, 
                SIGNED + LONG + LONG, SIGNED + LONG + LONG + INT:
            ty = TyLong
        case UNSIGNED + LONG, UNSIGNED + LONG + INT, 
               UNSIGNED + LONG + LONG, UNSIGNED + LONG + LONG + INT:
            ty = TyUlong
        case FLOAT:
            ty = TyFloat
        case DOUBLE:
            ty = TyDouble
        case LONG + DOUBLE:
            ty = TyLdouble
        default:
            ErrorTok(tok, "invalid type")
        }

        tok = tok.next
    }

    if isAtomic {
        ty = CopyType(ty)
        ty.isAtomic = true
    }

    rest = tok
    out = ty
    return
}

// func-params = ("void" | param ("," param)* ("," "...")?)? ")"
// param       = declspec declarator
func funcParams(tok *Token, ty *Type) (rest *Token, out *Type) {
    if Equal(tok, "void") && Equal(tok.next, ")") {
        rest = tok.next.next
        out = FuncType(ty)
        return
    }

    var head Type
    cur := &head
    isVariadic := false

    for !Equal(tok, ")") {
        if cur != &head {
            tok = Skip(tok, ",")
        }

        if Equal(tok, "...") {
            isVariadic = true
            tok = tok.next
            Skip(tok, ")")
            break
        }

        var ty2 *Type
        tok, ty2 = declspec(tok, nil)
        tok, ty2 = declarator(tok, ty2)

        name := ty2.name

        switch {
        case ty2.kind == TY_ARRAY:
            // "array of T" is converted to "pointer to T" only in the parameter
            // context. For example, *argv[] is converted to **argv by this.
            ty2 = PointerTo(ty2.base)
            ty2.name = name
        case ty2.kind == TY_FUNC:
            // Likewise, a function is converted to a pointer to a function
            // only in the parameter context.
            ty2 = PointerTo(ty2)
            ty2.name = name
        }

        cur.next = CopyType(ty2)
        cur = cur.next
    }

    if cur == &head {
        isVariadic = true
    }

    ty = FuncType(ty)
    ty.params = head.next
    ty.isVariadic = isVariadic
    rest = tok.next
    out = ty
    return
}

// array-dimensions = ("static" | "restrict")* const-expr? "]" type-suffix
func arrayDimensions(tok *Token, ty *Type) (rest *Token, out *Type) {
    for Equal(tok, "static") || Equal(tok, "restrict") {
        tok = tok.next
    }

    if Equal(tok, "]") {
        rest, ty = typeSuffix(tok.next, ty)
        out = ArrayOf(ty, -1)
        return
    }

    var expr *Node
    tok, expr = conditional(tok)
    tok = Skip(tok, "]")
    rest, ty = typeSuffix(tok, ty)

    if ty.kind == TY_VLA || !isConstExpr(expr) {
        out = VlaOf(ty, expr)
    } else {
        out = ArrayOf(ty, int(eval(expr)))
    }
    return 
}

// type-suffix = "(" func-params
//             | "[" array-dimensions
//             | 
func typeSuffix(tok *Token, ty *Type) (rest *Token, out *Type) {
    if Equal(tok, "(") {
        rest, out = funcParams(tok.next, ty)
        return
    }

    if Equal(tok, "[") {
        rest, out = arrayDimensions(tok.next, ty)
        return
    }

  rest = tok
  out = ty
  return
}

// pointers = ("*" ("const" | "volatile" | "restrict")*)*
func pointers(tok *Token, ty *Type) (rest *Token, out *Type) {
    for {
        var star bool
        tok, star = Consume(tok, "*")
        if !star {
            break
        }
        ty = PointerTo(ty)
        for EqualAny(tok, "const", "volatile", "restrict", "__restrict", "__restrict__") {
            tok = tok.next
        }
    }
    rest = tok
    out = ty
    return
}

// declarator = pointers ("(" ident ")" | "(" declarator ")" | ident) type-suffix
func declarator(tok *Token, ty *Type) (rest *Token, out *Type) {
    tok, ty = pointers(tok, ty)

    if Equal(tok, "(") {
        start := tok
        var dummy Type
        tok, _ = declarator(start.next, &dummy)
        tok = Skip(tok, ")")
        rest, ty = typeSuffix(tok, ty)
        tok, out = declarator(start.next, ty)
        return
    }

    var name *Token
    namePos := tok

    if tok.kind == TK_IDENT {
        name = tok
        tok = tok.next
    }

    rest, ty = typeSuffix(tok, ty)
    ty.name = name
    ty.namePos = namePos
    out = ty
    return
}

// abstract-declarator = pointers ("(" abstract-declarator ")")? type-suffix
func abstractDeclarator(tok *Token, ty *Type) (rest *Token, out *Type) {
    tok, ty = pointers(tok, ty)

    if Equal(tok, "(") {
        start := tok
        var dummy Type
        tok, _ = abstractDeclarator(start.next, &dummy)
        tok = Skip(tok, ")")
        rest, ty = typeSuffix(tok, ty)
        tok, out = abstractDeclarator(start.next, ty)
        return
    }

    rest, out = typeSuffix(tok, ty)
    return
}

// type-name = declspec abstract-declarator
func typename(tok *Token) (rest *Token, out *Type) {
    tok, ty := declspec(tok, nil)
    rest, out = abstractDeclarator(tok, ty)
    return
}

func isEnd(tok *Token) bool {
    return (Equal(tok, "}") || (Equal(tok, ",") && Equal(tok.next, "}")))
}

func consumeEnd(tok *Token) (*Token, bool) {
    if Equal(tok, "}") {
        return tok.next, true
    }
    if Equal(tok, ",") && Equal(tok.next, "}") {
        return tok.next.next, true
    }
    return tok, false
}

// enum-specifier = ident? "{" enum-list? "}"
//                | ident ("{" enum-list? "}")?
//
// enum-list      = ident ("=" num)? ("," ident ("=" num)?)* ","?
func enumSpecifier(tok *Token) (rest *Token, out *Type) {
    ty := EnumType()

    // Read a struct tag.
    var tag *Token
    if tok.kind == TK_IDENT {
        tag = tok
        tok = tok.next
    }

    if tag != nil && !Equal(tok, "{") {
        ty := findTag(tag)
        if ty == nil {
            ErrorTok(tag, "unknown enum type")
        }
        if ty.kind != TY_ENUM {
            ErrorTok(tag, "not an enum tag")
        }
        rest = tok
        out = ty
        return
    }

    tok = Skip(tok, "{")

    // Read an enum-list.
    i := 0
    val := 0
    for {
        var done bool
        rest, done = consumeEnd(tok)
        if done {
            break
        }

        if i > 0 {
            tok = Skip(tok, ",")
        }
        i++

        name := getIdent(tok)
        tok = tok.next

        if Equal(tok, "=") {
            var temp int64
            tok, temp = ConstExpr(tok.next)
            val = int(temp)
        }

        sc := pushScope(name)
        sc.enumTy = ty
        sc.enumVal = val
        val++
    }

    if tag != nil {
        pushTagScope(tag, ty)
    }

    out = ty
    return
}

// typeof-specifier = "(" (expr | typename) ")"
func typeofSpecifier(tok *Token) (rest *Token, out *Type) {
    tok = Skip(tok, "(")
    var ty *Type
    if isTypename(tok) {
        tok, ty = typename(tok)
    } else {
        var node *Node
        tok, node = expr(tok)
        AddType(node)
        ty = node.ty
    }
    rest = Skip(tok, ")")
    out = ty
    return
}

// Generates code for computing a VLA size.
func computeVlaSize(ty *Type, tok *Token) *Node {
    node := newNode(ND_NULL_EXPR, tok)
    if ty.base != nil {
        node = newBinary(ND_COMMA, node, computeVlaSize(ty.base, tok), tok)
    }

    if ty.kind != TY_VLA {
        return node
    }

    var baseSz *Node
    if ty.base.kind == TY_VLA {
        baseSz = newVarNode(ty.base.vlaSize, tok)
    } else {
        baseSz = newNum(int64(ty.base.size), tok)
    }

    ty.vlaSize = newLvar("", TyUlong)
    expr := 
        newBinary(
            ND_ASSIGN, 
            newVarNode(ty.vlaSize, tok),
            newBinary(ND_MUL, ty.vlaLen, baseSz, tok),
            tok)
    return newBinary(ND_COMMA, node, expr, tok)
}

func newAlloca(sz *Node) *Node {
    node := newUnary(ND_FUNCALL, newVarNode(builtinAlloca, sz.tok), sz.tok)
    node.funcTy = builtinAlloca.ty
    node.ty = builtinAlloca.ty.returnTy
    node.args = sz
    AddType(sz)
    return node
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
func declaration(tok *Token, basety *Type, attr *VarAttr) (rest *Token, out *Node) {
    var head Node
    cur := &head
    i := 0

    for !Equal(tok, ";") {
        if i > 0 {
            tok = Skip(tok, ",")
        }
        i++

        var ty *Type
        tok, ty = declarator(tok, basety)
        if ty.kind == TY_VOID {
            ErrorTok(tok, "variable declared void")
        }
        if ty.name == nil {
            ErrorTok(ty.namePos, "variable name omitted")
        }

        if attr != nil && attr.isStatic {
            // static local variable
            varObj := newAnonGvar(ty)
            sc := pushScope(getIdent(ty.name))
            sc.varObj = varObj
            if Equal(tok, "=") {
                tok = gvarInitializer(tok.next, varObj)
            }
            continue
        }

        // Generate code for computing a VLA size. We need to do this
        // even if ty is not VLA because ty may be a pointer to VLA
        // (e.g. int (*foo)[n][m] where n and m are variables.)
        cur.next = newUnary(ND_EXPR_STMT, computeVlaSize(ty, tok), tok)
        cur = cur.next

        if ty.kind == TY_VLA {
            if Equal(tok, "=") {
                ErrorTok(tok, "variable-sized object may not be initialized")
            }

            // Variable length arrays (VLAs) are translated to alloca() calls.
            // For example, `int x[n+2]` is translated to `tmp = n + 2,
            // x = alloca(tmp)`.
            varObj := newLvar(getIdent(ty.name), ty)
            tok := ty.name // TODO: Rename 'tok'?
            expr := 
                newBinary(
                    ND_ASSIGN, 
                    newVlaPtr(varObj, tok),
                    newAlloca(newVarNode(ty.vlaSize, tok)),
                    tok)

            cur.next = newUnary(ND_EXPR_STMT, expr, tok)
            cur = cur.next
            continue
        }

        varObj := newLvar(getIdent(ty.name), ty)
        if attr != nil && attr.align != 0 {
            varObj.align = attr.align
        }

        if Equal(tok, "=") {
            var expr *Node
            tok, expr = lvarInitializer(tok.next, varObj)
            cur.next = newUnary(ND_EXPR_STMT, expr, tok)
            cur = cur.next
        }

        if varObj.ty.size < 0 {
            ErrorTok(ty.name, "variable has incomplete type")
        }
        if varObj.ty.kind == TY_VOID {
            ErrorTok(ty.name, "variable declared void")
        }
    }

    node := newNode(ND_BLOCK, tok)
    node.body = head.next
    rest = tok.next
    out = node
    return
}

func skipExcessElement(tok *Token) *Token {
    if Equal(tok, "{") {
        tok = skipExcessElement(tok.next)
        return Skip(tok, "}")
    }
    tok, _ = assign(tok)
    return tok
}

// string-initializer = string-literal
func stringInitializer(tok *Token, init *Initializer) *Token {
    if init.isFlexible {
        *init = *newInitializer(ArrayOf(init.ty.base, tok.ty.arrayLen), false)
    }

    n := IntMin(init.ty.arrayLen, tok.ty.arrayLen)

    switch init.ty.base.size {
    case 1:
        str := tok.str
        for i := 0; i < n; i++ {
            init.children[i].expr = newNum(int64(str[i]), tok)
        }
    case 2:
        utf16 := tok.utf16
        for i := 0; i < n; i++ {
            init.children[i].expr = newNum(int64(utf16[i]), tok)
        }
    case 4:
        utf32 := tok.utf32
        for i := 0; i < n; i++ {
            init.children[i].expr = newNum(int64(utf32[i]), tok)
        }
    default:
        Unreachable()
    }

    return tok.next
}

// array-designator = "[" const-expr "]"
//
// C99 added the designated initializer to the language, which allows
// programmers to move the "cursor" of an initializer to any element.
// The syntax looks like this:
//
//   int x[10] = { 1, 2, [5]=3, 4, 5, 6, 7 };
//
// `[5]` moves the cursor to the 5th element, so the 5th element of x
// is set to 3. Initialization then continues forward in order, so
// 6th, 7th, 8th and 9th elements are initialized with 4, 5, 6 and 7,
// respectively. Unspecified elements (in this case, 3rd and 4th
// elements) are initialized with zero.
//
// Nesting is allowed, so the following initializer is valid:
//
//   int x[5][10] = { [5][8]=1, 2, 3 };
//
// It sets x[5][8], x[5][9] and x[6][0] to 1, 2 and 3, respectively.
//
// Use `.fieldname` to move the cursor for a struct initializer. E.g.
//
//   struct { int a, b, c; } x = { .c=5 };
//
// The above initializer sets x.c to 5.
func arrayDesignator(tok *Token, ty *Type) (rest *Token, begin int, end int) {
    var temp int64
    tok, temp = ConstExpr(tok.next)
    begin = int(temp)
    if begin >= ty.arrayLen {
        ErrorTok(tok, "array designator index exceeds array bounds")
    }

    if Equal(tok, "...") {
        tok, temp = ConstExpr(tok.next)
        end = int(temp)
        if end >= ty.arrayLen {
            ErrorTok(tok, "array designator index exceeds array bounds")
        }
        if end < begin {
            ErrorTok(tok, "array designator range [%d, %d] is empty", begin, end)
        }
    } else {
        end = begin
    }

    rest = Skip(tok, "]")
    return
}

// struct-designator = "." ident
func structDesignator(tok *Token, ty *Type) (rest *Token, out *Member) {
    start := tok
    tok = Skip(tok, ".")
    if tok.kind != TK_IDENT {
        ErrorTok(tok, "expected a field designator")
    }

    for mem := ty.members; mem != nil; mem = mem.next {
        // Anonymous struct member
        if mem.ty.kind == TY_STRUCT && mem.name == nil {
            if getStructMember(mem.ty, tok) != nil {
                rest = start
                out = mem
                return
            }
            continue
        }

        // Regular struct member
        if string(mem.name.text) == string(tok.text) {
            rest = tok.next
            out = mem
            return
        }
    }

    ErrorTok(tok, "struct has no such member")
    return
}

// designation = ("[" const-expr "]" | "." ident)* "="? initializer
func designation(tok *Token, init *Initializer) *Token {
    if Equal(tok, "[") {
        if init.ty.kind != TY_ARRAY {
            ErrorTok(tok, "array index in non-array initializer")
        }

        var begin, end int
        tok, begin, end = arrayDesignator(tok, init.ty)

        var tok2 *Token
        for i := begin; i <= end; i++ {
            tok2 = designation(tok, init.children[i])
        }
        return arrayInitializer2(tok2, init, begin+1)
    }

    if Equal(tok, ".") && init.ty.kind == TY_STRUCT {
        var mem *Member
        tok, mem = structDesignator(tok, init.ty)
        tok = designation(tok, init.children[mem.idx])
        init.expr = nil
        return structInitializer2(tok, init, mem.next)
    }

    if Equal(tok, ".") && init.ty.kind == TY_UNION {
        var mem *Member
        tok, mem = structDesignator(tok, init.ty)
        init.mem = mem
        return designation(tok, init.children[mem.idx])
    }

    if Equal(tok, ".") {
        ErrorTok(tok, "field name not in struct or union initializer")
    }

    if Equal(tok, "=") {
        tok = tok.next
    }
    return initializer2(tok, init)
}

// An array length can be omitted if an array has an initializer
// (e.g. `int x[] = {1,2,3}`). If it's omitted, count the number
// of initializer elements.
func countArrayInitElements(tok *Token, ty *Type) int {
    first := true
    dummy := newInitializer(ty.base, true)

    i := 0
    max := 0

    for {
        var done bool
        tok, done = consumeEnd(tok)
        if done {
            break
        }

        if !first {
            tok = Skip(tok, ",")
        }
        first = false

        if Equal(tok, "[") {
            var temp int64
            tok, temp = ConstExpr(tok.next)
            i = int(temp)
            if Equal(tok, "...") {
                tok, temp = ConstExpr(tok.next)
                i = int(temp)
            }
            tok = Skip(tok, "]")
            tok = designation(tok, dummy)
        } else {
            tok = initializer2(tok, dummy)
        }

        i++
        max = IntMax(max, i)
    }

    return max
}

// array-initializer1 = "{" initializer ("," initializer)* ","? "}"
func arrayInitializer1(tok *Token, init *Initializer) *Token {
    var rest *Token
    tok = Skip(tok, "{")

    if init.isFlexible {
        n := countArrayInitElements(tok, init.ty)
        *init = *newInitializer(ArrayOf(init.ty.base, n), false)
    }

    first := true

    if init.isFlexible {
        n := countArrayInitElements(tok, init.ty)
        *init = *newInitializer(ArrayOf(init.ty.base, n), false)
    }

    for i := 0; ; i++ {
        var done bool
        rest, done = consumeEnd(tok)
        if done {
            break
        }
    
        if !first {
            tok = Skip(tok, ",")
        }
        first = false

        if Equal(tok, "[") {
            var begin, end int
            tok, begin, end = arrayDesignator(tok, init.ty)
            var tok2 *Token
            for j := begin; j <= end; j++ {
                tok2 = designation(tok, init.children[j])
            }
            tok = tok2
            i = end
            continue
        }

        if i < init.ty.arrayLen {
            tok = initializer2(tok, init.children[i])
        } else {
            tok = skipExcessElement(tok)
        }
    }

    return rest
}

// array-initializer2 = initializer ("," initializer)*
func arrayInitializer2(tok *Token, init *Initializer, i int) *Token {
    if init.isFlexible {
        n := countArrayInitElements(tok, init.ty)
        *init = *newInitializer(ArrayOf(init.ty.base, n), false)
    }

    for ; i < init.ty.arrayLen && !isEnd(tok); i++ {
        start := tok
        if i > 0 {
            tok = Skip(tok, ",")
        }
        if Equal(tok, "[") || Equal(tok, ".") {
            return start
        }
        tok = initializer2(tok, init.children[i])
    }
    return tok
}

// struct-initializer1 = "{" initializer ("," initializer)* ","? "}"
func structInitializer1(tok *Token, init *Initializer) *Token {
    var rest *Token
    tok = Skip(tok, "{")

    mem := init.ty.members
    first := true

    for {
        var done bool
        rest, done = consumeEnd(tok)
        if done {
            break
        }

        if !first {
            tok = Skip(tok, ",")
        }
        first = false

        if Equal(tok, ".") {
            tok, mem = structDesignator(tok, init.ty)
            tok = designation(tok, init.children[mem.idx])
            mem = mem.next
            continue
        }

        if mem != nil {
            tok = initializer2(tok, init.children[mem.idx])
            mem = mem.next
        } else {
            tok = skipExcessElement(tok)
        }
    }

    return rest
}

// struct-initializer2 = initializer ("," initializer)*
func structInitializer2(tok *Token, init *Initializer, mem *Member) *Token {
    first := true

    for ; mem != nil && !isEnd(tok); mem = mem.next {
        start := tok
        if !first {
            tok = Skip(tok, ",")
        }
        first = false
        if Equal(tok, "[") || Equal(tok, ".") {
            return start
        }
        tok = initializer2(tok, init.children[mem.idx])
    }
    return tok
}

func unionInitializer(tok *Token, init *Initializer) *Token {
    var rest *Token

    // Unlike structs, union initializers take only one initializer,
    // and that initializes the first union member by default.
    // You can initialize other member using a designated initializer.
    if Equal(tok, "{") && Equal(tok.next, ".") {
        var mem *Member
        tok, mem = structDesignator(tok.next, init.ty)
        init.mem = mem
        tok = designation(tok, init.children[mem.idx])
        rest = Skip(tok, "}")
        return rest
    }

    init.mem = init.ty.members

    if Equal(tok, "{") {
        tok = initializer2(tok.next, init.children[0])
        tok, _ = Consume(tok, ",")
        rest = Skip(tok, "}")
    } else {
        rest = initializer2(tok, init.children[0])
    }

    return rest
}

// initializer = string-initializer | array-initializer
//             | struct-initializer | union-initializer
//             | assign
func initializer2(tok *Token, init *Initializer) *Token {
    var rest *Token

    if init.ty.kind == TY_ARRAY && tok.kind == TK_STR {
        rest = stringInitializer(tok, init)
        return rest
    }

    if init.ty.kind == TY_ARRAY {
        if Equal(tok, "{") {
            rest = arrayInitializer1(tok, init)
        } else {
            rest = arrayInitializer2(tok, init, 0)
        }
        return rest
    }

    if init.ty.kind == TY_STRUCT {
        if Equal(tok, "{") {
            rest = structInitializer1(tok, init)
            return rest
        }

        // A struct can be initialized with another struct. E.g.
        // `struct T x = y;` where y is a variable of type `struct T`.
        // Handle that case first.
        var expr *Node
        rest, expr = assign(tok)
        AddType(expr)
        if expr.ty.kind == TY_STRUCT {
            init.expr = expr
            return rest
        }

        rest = structInitializer2(tok, init, init.ty.members)
        return rest
    }

    if init.ty.kind == TY_UNION {
        rest = unionInitializer(tok, init)
        return rest
    }

    if Equal(tok, "{") {
        // An initializer for a scalar variable can be surrounded by
        // braces. E.g. `int x = {3};`. Handle that case.
        tok = initializer2(tok.next, init)
        rest = Skip(tok, "}")
        return rest
    }

    rest, init.expr = assign(tok)
    return rest
}

func copyStructType(ty *Type) *Type {
    ty = CopyType(ty)

    var head Member
    cur := &head
    for mem := ty.members; mem != nil; mem = mem.next {
        m := new(Member)
        *m = *mem
        cur.next = m
        cur = cur.next
    }

    ty.members = head.next
    return ty
}

func initializer(tok *Token, ty *Type) (rest *Token, init *Initializer, newTy *Type) {
    init = newInitializer(ty, true)
    rest = initializer2(tok, init)

    if (ty.kind == TY_STRUCT || ty.kind == TY_UNION) && ty.isFlexible {
        ty = copyStructType(ty)

        mem := ty.members
        for mem.next != nil {
            mem = mem.next
        }
        mem.ty = init.children[mem.idx].ty
        ty.size += mem.ty.size

        newTy = ty
        return
    }

    newTy = init.ty
    return
}

func initDesgExpr(desg *InitDesg, tok *Token) *Node {
    if desg.varObj != nil {
        return newVarNode(desg.varObj, tok)
    }

    if desg.member != nil {
        node := newUnary(ND_MEMBER, initDesgExpr(desg.next, tok), tok)
        node.member = desg.member
        return node
    }

    lhs := initDesgExpr(desg.next, tok)
    rhs := newNum(int64(desg.idx), tok)
    return newUnary(ND_DEREF, newAdd(lhs, rhs, tok), tok)
}

func createLvarInit(init *Initializer, ty *Type, desg *InitDesg, tok *Token) *Node {
    if ty.kind == TY_ARRAY {
        node := newNode(ND_NULL_EXPR, tok)
        for i := 0; i < ty.arrayLen; i++ {
            desg2 := InitDesg{next: desg, idx: i}
            rhs := createLvarInit(init.children[i], ty.base, &desg2, tok)
            node = newBinary(ND_COMMA, node, rhs, tok)
        }
        return node
    }

    if ty.kind == TY_STRUCT && init.expr == nil {
        node := newNode(ND_NULL_EXPR, tok)
        for mem := ty.members; mem != nil; mem = mem.next {
            desg2 := InitDesg{next: desg, idx: 0, member: mem}
            rhs := createLvarInit(init.children[mem.idx], mem.ty, &desg2, tok)
            node = newBinary(ND_COMMA, node, rhs, tok)
        }
        return node
    }

    if ty.kind == TY_UNION {
        mem := init.mem
        if mem == nil {
            mem = ty.members
        }
        desg2 := InitDesg{next: desg, idx: 0, member: mem}
        return createLvarInit(init.children[mem.idx], mem.ty, &desg2, tok)
    }

    if init.expr == nil {
        return newNode(ND_NULL_EXPR, tok)
    }

    lhs := initDesgExpr(desg, tok)
    return newBinary(ND_ASSIGN, lhs, init.expr, tok)
}

// A variable definition with an initializer is a shorthand notation
// for a variable definition followed by assignments. This function
// generates assignment expressions for an initializer. For example,
// `int x[2][2] = {{6, 7}, {8, 9}}` is converted to the following
// expressions:
//
//   x[0][0] = 6;
//   x[0][1] = 7;
//   x[1][0] = 8;
//   x[1][1] = 9;
func lvarInitializer(tok *Token, varObj *Obj) (rest *Token, out *Node) {
    var init *Initializer
    rest, init, varObj.ty = initializer(tok, varObj.ty)
    var desg = InitDesg{next: nil, idx: 0, member: nil, varObj: varObj}

    // If a partial initializer list is given, the standard requires
    // that unspecified elements are set to 0. Here, we simply
    // zero-initialize the entire memory region of a variable before
    // initializing it with user-supplied values.
    lhs := newNode(ND_MEMZERO, tok)
    lhs.varObj = varObj

    rhs := createLvarInit(init, varObj.ty, &desg, tok)
    out = newBinary(ND_COMMA, lhs, rhs, tok)
    return
}

func readBuf(buf []byte, sz int) uint64 {
    switch sz {
    case 1:
        return uint64(buf[0])
    case 2:
        return uint64(buf[0]) | (uint64(buf[1]) << 8)
    case 4:
        return uint64(buf[0]) | (uint64(buf[1]) << 8) | 
            (uint64(buf[2]) << 16) | (uint64(buf[3]) << 24)
    case 8:
        return uint64(buf[0]) | (uint64(buf[1]) << 8) | 
            (uint64(buf[2]) << 16) | (uint64(buf[3]) << 24) |
            (uint64(buf[4]) << 32) | (uint64(buf[5]) << 40) |
            (uint64(buf[6]) << 48) | (uint64(buf[7]) << 56)
    default:
        Unreachable()
        return 0
    }
}

func writeBuf(buf []byte, val uint64, sz int) {
    switch sz {
    case 1:
        buf[0] = byte(val)
    case 2:
        buf[0] = byte(val)
        buf[1] = byte(val>>8)
    case 4:
        buf[0] = byte(val)
        buf[1] = byte(val>>8)
        buf[2] = byte(val>>16)
        buf[3] = byte(val>>24)
    case 8:
        buf[0] = byte(val)
        buf[1] = byte(val>>8)
        buf[2] = byte(val>>16)
        buf[3] = byte(val>>24)
        buf[4] = byte(val>>32)
        buf[5] = byte(val>>40)
        buf[6] = byte(val>>48)
        buf[7] = byte(val>>56)
    default:
        Unreachable()
    }
}

func writeGvarData(
        cur *Relocation, 
        init *Initializer, 
        ty *Type, 
        buf []byte, 
        offset int) *Relocation {
    if ty.kind == TY_ARRAY {
        sz := ty.base.size
        for i := 0; i < ty.arrayLen; i++ {
            cur = writeGvarData(cur, init.children[i], ty.base, buf, offset+sz*i)
        }
        return cur
    }

    if ty.kind == TY_STRUCT {
        for mem := ty.members; mem != nil; mem = mem.next {
            if mem.isBitfield {
                expr := init.children[mem.idx].expr
                if expr == nil {
                    break
                }

                loc := buf[offset+mem.offset:]
                oldval := readBuf(loc, mem.ty.size)
                newval := uint64(eval(expr))
                mask := (uint64(1) << mem.bitWidth) - 1
                combined := oldval | ((newval & mask) << mem.bitOffset)
                writeBuf(loc, combined, mem.ty.size)
            } else {
                cur = 
                    writeGvarData(
                        cur, 
                        init.children[mem.idx], 
                        mem.ty, 
                        buf, 
                        offset+mem.offset)
            }
        }
        return cur
    }

    if ty.kind == TY_UNION {
        if init.mem == nil {
            return cur
        }
        return writeGvarData(
            cur, 
            init.children[init.mem.idx], 
            init.mem.ty, 
            buf, 
            offset)
    }

    if init.expr == nil {
        return cur
    }

    if ty.kind == TY_FLOAT {
        EncodeFloat(buf[offset:], float32(evalDouble(init.expr)))
        return cur
    }

    if ty.kind == TY_DOUBLE {
        EncodeDouble(buf[offset:], evalDouble(init.expr))
        return cur
    }

    val, label := eval2(init.expr)
    if label == nil {
        writeBuf(buf[offset:], uint64(val), ty.size)
        return cur
    }

    rel := new(Relocation)
    rel.offset = offset
    rel.label = label
    rel.addend = val
    cur.next = rel
    return cur.next
}

// Initializers for global variables are evaluated at compile-time and
// embedded to .data section. This function serializes Initializer
// objects to a flat byte array. It is a compile error if an
// initializer list contains a non-constant expression.
func gvarInitializer(tok *Token, varObj *Obj) *Token {
    rest, init, ty := initializer(tok, varObj.ty)
    varObj.ty = ty

    var head Relocation
    buf := make([]byte, varObj.ty.size)
    writeGvarData(&head, init, varObj.ty, buf, 0)
    varObj.initData = buf
    varObj.rel = head.next

    return rest
}

var typenameTable = map[string]bool{
    "void": true, 
    "_Bool": true, 
    "char": true, 
    "short": true, 
    "int": true, 
    "long": true, 
    "struct": true, 
    "union": true,
    "typedef": true, 
    "enum": true, 
    "static": true, 
    "extern": true, 
    "_Alignas": true, 
    "signed": true, 
    "unsigned": true,
    "const": true, 
    "volatile": true, 
    "auto": true, 
    "register": true, 
    "restrict": true, 
    "__restrict": true,
    "__restrict__": true, 
    "_Noreturn": true, 
    "float": true, 
    "double": true, 
    "typeof": true, 
    "inline": true,
    "_Thread_local": true, 
    "__thread": true, 
    "_Atomic": true,
}

// Returns true if a given token represents a type.
func isTypename(tok *Token) bool {
    return (typenameTable[string(tok.text)] || findTypedef(tok) != nil)
}

// asm-stmt = "asm" ("volatile" | "inline")* "(" string-literal ")"
func asmStmt(tok *Token) (rest *Token, out *Node) {
    node := newNode(ND_ASM, tok)
    tok = tok.next

    for Equal(tok, "volatile") || Equal(tok, "inline") {
        tok = tok.next
    }

    tok = Skip(tok, "(")
    if tok.kind != TK_STR || tok.ty.base.kind != TY_CHAR {
        ErrorTok(tok, "expected string literal")
    }
    node.asmStr = GetStr(tok)
    rest = Skip(tok.next, ")")
    out = node
    return
}

// stmt = "return" expr? ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "switch" "(" expr ")" stmt
//      | "case" const-expr ("..." const-expr)? ":" stmt
//      | "default" ":" stmt
//      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "do" stmt "while" "(" expr ")" ";"
//      | "asm" asm-stmt
//      | "goto" (ident | "*" expr) ";"
//      | "break" ";"
//      | "continue" ";"
//      | ident ":" stmt
//      | "{" compound-stmt
//      | expr-stmt
func stmt(tok *Token) (rest *Token, out *Node) {
    if Equal(tok, "return") {
        node := newNode(ND_RETURN, tok)
        var done bool
        rest, done = Consume(tok.next, ";")
        if done {
            out = node
            return
        }

        var exp *Node
        tok, exp = expr(tok.next)
        rest = Skip(tok, ";")

        AddType(exp)
        ty := currentFn.ty.returnTy
        if ty.kind != TY_STRUCT && ty.kind != TY_UNION {
            exp = NewCast(exp, currentFn.ty.returnTy)
        }

        node.lhs = exp
        out = node
        return
    }

    if Equal(tok, "if") {
        node := newNode(ND_IF, tok)
        tok = Skip(tok.next, "(")
        tok, node.cond = expr(tok)
        tok = Skip(tok, ")")
        tok, node.then = stmt(tok)
        if Equal(tok, "else") {
            tok, node.els = stmt(tok.next)
        }
        rest = tok
        out = node
        return
    }

    if Equal(tok, "switch") {
        node := newNode(ND_SWITCH, tok)
        tok = Skip(tok.next, "(")
        tok, node.cond = expr(tok)
        tok = Skip(tok, ")")

        sw := currentSwitch
        currentSwitch = node

        brk := brkLabel
        node.brkLabel = newUniqueName()
        brkLabel = node.brkLabel

        rest, node.then = stmt(tok)

        currentSwitch = sw
        brkLabel = brk
        out = node
        return
    }

    if Equal(tok, "case") {
        if currentSwitch == nil {
            ErrorTok(tok, "stray case")
        }

        node := newNode(ND_CASE, tok)
        var begin, end int64
        tok, begin = ConstExpr(tok.next)

        if Equal(tok, "...") {
            // [GNU] Case ranges, e.g. "case 1 ... 5:"
            tok, end = ConstExpr(tok.next)
            if end < begin {
                ErrorTok(tok, "empty case range specified")
            }
        } else {
            end = begin
        }

        tok = Skip(tok, ":")
        node.label = newUniqueName()
        rest, node.lhs = stmt(tok)
        node.begin = begin
        node.end = end
        node.caseNext = currentSwitch.caseNext
        currentSwitch.caseNext = node
        out = node
        return
    }

    if Equal(tok, "default") {
        if currentSwitch == nil {
            ErrorTok(tok, "stray default")
        }

        node := newNode(ND_CASE, tok)
        tok = Skip(tok.next, ":")
        node.label = newUniqueName()
        rest, node.lhs = stmt(tok)
        currentSwitch.defaultCase = node
        out = node
        return
    }

    if Equal(tok, "for") {
        node := newNode(ND_FOR, tok)
        tok = Skip(tok.next, "(")

        enterScope()

        brk := brkLabel
        cont := contLabel
        node.brkLabel = newUniqueName()
        brkLabel = node.brkLabel
        node.contLabel = newUniqueName()
        contLabel = node.contLabel

        if isTypename(tok) {
            var basety *Type
            tok, basety = declspec(tok, nil)
            tok, node.init = declaration(tok, basety, nil)
        } else {
            tok, node.init = exprStmt(tok)
        }

        if !Equal(tok, ";") {
            tok, node.cond = expr(tok)
        }
        tok = Skip(tok, ";")

        if !Equal(tok, ")") {
            tok, node.inc = expr(tok)
        }
        tok = Skip(tok, ")")

        rest, node.then = stmt(tok)

        leaveScope()
        brkLabel = brk
        contLabel = cont
        out = node
        return
    }

    if Equal(tok, "while") {
        node := newNode(ND_FOR, tok)
        tok = Skip(tok.next, "(")
        tok, node.cond = expr(tok)
        tok = Skip(tok, ")")

        brk := brkLabel
        cont := contLabel
        node.brkLabel = newUniqueName()
        brkLabel = node.brkLabel
        node.contLabel = newUniqueName()
        contLabel = node.contLabel

        rest, node.then = stmt(tok)

        brkLabel = brk
        contLabel = cont
        out = node
        return
    }

    if Equal(tok, "do") {
        node := newNode(ND_DO, tok)

        brk := brkLabel
        cont := contLabel
        node.brkLabel = newUniqueName()
        brkLabel = node.brkLabel
        node.contLabel = newUniqueName()
        contLabel = node.contLabel

        tok, node.then = stmt(tok.next)

        brkLabel = brk
        contLabel = cont

        tok = Skip(tok, "while")
        tok = Skip(tok, "(")
        tok, node.cond = expr(tok)
        tok = Skip(tok, ")")
        rest = Skip(tok, ";")
        out = node
        return
    }

    if Equal(tok, "asm") {
        rest, out = asmStmt(tok)
        return
    }

    if Equal(tok, "goto") {
        if Equal(tok.next, "*") {
            // [GNU] `goto *ptr` jumps to the address specified by `ptr`.
            node := newNode(ND_GOTO_EXPR, tok)
            tok, node.lhs = expr(tok.next.next)
            rest = Skip(tok, ";")
            out = node
            return
        }

        node := newNode(ND_GOTO, tok)
        node.label = getIdent(tok.next)
        node.gotoNext = gotos
        gotos = node
        rest = Skip(tok.next.next, ";")
        out = node
        return
    }

    if Equal(tok, "break") {
        if len(brkLabel) == 0 {
            ErrorTok(tok, "stray break")
        }
        node := newNode(ND_GOTO, tok)
        node.uniqueLabel = brkLabel
        rest = Skip(tok.next, ";")
        out = node
        return
    }

    if Equal(tok, "continue") {
        if len(contLabel) == 0 {
            ErrorTok(tok, "stray continue")
        }
        node := newNode(ND_GOTO, tok)
        node.uniqueLabel = contLabel
        rest = Skip(tok.next, ";")
        out = node
        return
    }

    if tok.kind == TK_IDENT && Equal(tok.next, ":") {
        node := newNode(ND_LABEL, tok)
        node.label = string(tok.text)
        node.uniqueLabel = newUniqueName()
        rest, node.lhs = stmt(tok.next.next)
        node.gotoNext = labels
        labels = node
        out = node
        return
    }

    if Equal(tok, "{") {
        rest, out = compoundStmt(tok.next)
        return
    }

    rest, out = exprStmt(tok)
    return
}

// compound-stmt = (typedef | declaration | stmt)* "}"
func compoundStmt(tok *Token) (rest *Token, out *Node) {
    node := newNode(ND_BLOCK, tok)
    var head Node
    cur := &head

    enterScope()

    for !Equal(tok, "}") {
        if isTypename(tok) && !Equal(tok.next, ":") {
            var attr VarAttr
            var basety *Type
            tok, basety = declspec(tok, &attr)

            if attr.isTypedef {
                tok = parseTypedef(tok, basety)
                continue
            }

            if isFunction(tok) {
                tok = function(tok, basety, &attr)
                continue
            }

            if attr.isExtern {
                tok = globalVariable(tok, basety, &attr)
                continue
            }

            tok, cur.next = declaration(tok, basety, &attr)
            cur = cur.next
        } else {
            tok, cur.next = stmt(tok)
            cur = cur.next
        }

        AddType(cur)
    }

    leaveScope()

    node.body = head.next
    rest = tok.next
    out = node
    return
}

// expr-stmt = expr? ";"
func exprStmt(tok *Token) (rest *Token, out *Node) {
    if Equal(tok, ";") {
        rest = tok.next
        out = newNode(ND_BLOCK, tok)
        return
    }

    node := newNode(ND_EXPR_STMT, tok)
    tok, node.lhs = expr(tok)
    rest = Skip(tok, ";")
    out = node
    return
}

// expr = assign ("," expr)?
func expr(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = assign(tok)

    if Equal(tok, ",") {
        var node2 *Node
        rest, node2 = expr(tok.next)
        out = newBinary(ND_COMMA, node, node2, tok)
        return
    }

    rest = tok
    out = node
    return
}

func eval(node *Node) int64 {
    // TODO: The original code checks for label pointer != NULL in
    //     eval2 - but misses this check for ND_LABEL_VAL.
    //     This check is actually redundant - but notify the author anyway.
    val, label := eval2(node)
    if label != nil {
        ErrorTok(node.tok, "not a compile-time constant")
    }
    return val
}

// Evaluate a given node as a constant expression.
//
// A constant expression is either just a number or ptr+n where ptr
// is a pointer to a global variable and n is a postiive/negative
// number. The latter form is accepted only as an initialization
// expression for a global variable.
func eval2(node *Node) (val int64, label *string) {
    toBool := func(x int64) bool {
        return (x != 0)
    }
    toInt := func(x bool) int64 {
        if x {
            return 1
        } else {
            return 0
        }
    }

    AddType(node)

    if IsFlonum(node.ty) {
        val = int64(evalDouble(node))
        return
    }

    switch node.kind {
    case ND_ADD:
        val, label = eval2(node.lhs)
        val += eval(node.rhs)
        return
    case ND_SUB:
        val, label = eval2(node.lhs)
        val -= eval(node.rhs)
        return
    case ND_MUL:
        val, label = eval2(node.lhs)
        val *= eval(node.rhs)
        return
    case ND_DIV:
        if (node.ty.isUnsigned) {
            val = int64(uint64(eval(node.lhs)) / uint64(eval(node.rhs)))
        } else {
            val = eval(node.lhs) / eval(node.rhs)
        }
        return
    case ND_NEG:
        val = -eval(node.lhs)
        return
    case ND_MOD:
        if node.ty.isUnsigned {
            val = int64(uint64(eval(node.lhs)) % uint64(eval(node.rhs)))
        } else {
            val = eval(node.lhs) % eval(node.rhs)
        }
        return
    case ND_BITAND:
        val = eval(node.lhs) & eval(node.rhs)
        return
    case ND_BITOR:
        val = eval(node.lhs) | eval(node.rhs)
        return
    case ND_BITXOR:
        val = eval(node.lhs) ^ eval(node.rhs)
        return
    case ND_SHL:
        val = eval(node.lhs) << eval(node.rhs)
        return
    case ND_SHR:
        if node.ty.isUnsigned && node.ty.size == 8 {
            val = int64(uint64(eval(node.lhs)) >> uint64(eval(node.rhs)))
        } else {
            val = eval(node.lhs) >> eval(node.rhs)
        }
        return
    case ND_EQ:
        val = toInt(eval(node.lhs) == eval(node.rhs))
        return
    case ND_NE:
        val = toInt(eval(node.lhs) != eval(node.rhs))
        return
    case ND_LT:
        if node.lhs.ty.isUnsigned {
            val = toInt(uint64(eval(node.lhs)) < uint64(eval(node.rhs)))
        } else {
            val = toInt(eval(node.lhs) < eval(node.rhs))
        }
        return
    case ND_LE:
        if node.lhs.ty.isUnsigned {
            val = toInt(uint64(eval(node.lhs)) <= uint64(eval(node.rhs)))
        } else {
            val = toInt(eval(node.lhs) <= eval(node.rhs))
        }
        return
    case ND_COND:
        if toBool(eval(node.cond)) {
            val, label = eval2(node.then)
        } else {
            val, label = eval2(node.els)
        }
        return
    case ND_COMMA:
        val, label = eval2(node.rhs)
        return
    case ND_NOT:
        val = toInt(!toBool(eval(node.lhs)))
        return
    case ND_BITNOT:
        val = ^eval(node.lhs)
        return
    case ND_LOGAND:
        val = toInt(toBool(eval(node.lhs)) && toBool(eval(node.rhs)))
        return
    case ND_LOGOR:
        val = toInt(toBool(eval(node.lhs)) || toBool(eval(node.rhs)))
        return
    case ND_CAST:
        val, label = eval2(node.lhs)
        if IsInteger(node.ty) {
            switch node.ty.size {
            case 1: 
                if node.ty.isUnsigned {
                    val = int64(uint8(val))
                } else {
                    val = int64(int8(val))
                }
            case 2: 
                if node.ty.isUnsigned {
                    val = int64(uint16(val))
                } else {
                    val = int64(int16(val))
                }
            case 4: 
                if node.ty.isUnsigned {
                    val = int64(uint32(val))
                } else {
                    val = int64(int32(val))
                }
            }
        }
        return
    case ND_ADDR:
        val, label = evalRval(node.lhs)
        return
    case ND_LABEL_VAL:
        label = &node.uniqueLabel
        val = 0
        return
    case ND_MEMBER:
        if node.ty.kind != TY_ARRAY {
            ErrorTok(node.tok, "invalid initializer")
        }
        val, label = evalRval(node.lhs)
        val += int64(node.member.offset)
        return
    case ND_VAR:
        if node.varObj.ty.kind != TY_ARRAY && node.varObj.ty.kind != TY_FUNC {
            ErrorTok(node.tok, "invalid initializer")
        }
        label = &node.varObj.name
        val = 0
        return
    case ND_NUM:
        val = node.val
        return
    }

    ErrorTok(node.tok, "not a compile-time constant")

    return
}

func evalRval(node *Node) (val int64, label *string) {
    switch node.kind {
    case ND_VAR:
        if node.varObj.isLocal {
            ErrorTok(node.tok, "not a compile-time constant")
        }
        label = &node.varObj.name
        val = 0
        return
    case ND_DEREF:
        val, label = eval2(node.lhs)
        return
    case ND_MEMBER:
        val, label = evalRval(node.lhs)
        val += int64(node.member.offset)
        return
    }

    ErrorTok(node.tok, "invalid initializer")

    return
}

func isConstExpr(node *Node) bool {
    AddType(node)

    switch node.kind {
    case ND_ADD, 
            ND_SUB,
            ND_MUL,
            ND_DIV,
            ND_BITAND,
            ND_BITOR,
            ND_BITXOR,
            ND_SHL,
            ND_SHR,
            ND_EQ,
            ND_NE,
            ND_LT,
            ND_LE,
            ND_LOGAND,
            ND_LOGOR:
        return isConstExpr(node.lhs) && isConstExpr(node.rhs)
    case ND_COND:
        if !isConstExpr(node.cond) {
            return false
        }
        if eval(node.cond) != 0 {
            return isConstExpr(node.then)
        } else {
            return isConstExpr(node.els)
        }
    case ND_COMMA:
        return isConstExpr(node.rhs)
    case ND_NEG,
            ND_NOT,
            ND_BITNOT,
            ND_CAST:
        return isConstExpr(node.lhs)
    case ND_NUM:
        return true
    }

    return false
}

func ConstExpr(tok *Token) (rest *Token, val int64) {
    var node *Node
    rest, node = conditional(tok)
    val = eval(node)
    return
}

func evalDouble(node *Node) float64 {
    AddType(node)

    if IsInteger(node.ty) {
        if node.ty.isUnsigned {
            return float64(uint64(eval(node)))
        }
        return float64(eval(node))
    }

    switch node.kind {
    case ND_ADD:
        return evalDouble(node.lhs) + evalDouble(node.rhs)
    case ND_SUB:
        return evalDouble(node.lhs) - evalDouble(node.rhs)
    case ND_MUL:
        return evalDouble(node.lhs) * evalDouble(node.rhs)
    case ND_DIV:
        return evalDouble(node.lhs) / evalDouble(node.rhs)
    case ND_NEG:
        return -evalDouble(node.lhs)
    case ND_COND:
/* TODO: Original code says eval_double - shall be just eval
        if evalDouble(node.cond) != 0.0 {
*/
        if eval(node.cond) != 0 {
            return evalDouble(node.then)
        } else {
            return evalDouble(node.els)
        }
    case ND_COMMA:
        return evalDouble(node.rhs)
    case ND_CAST:
        if IsFlonum(node.lhs.ty) {
            return evalDouble(node.lhs)
        }
        return float64(eval(node.lhs))
    case ND_NUM:
        return node.fval
    }

    ErrorTok(node.tok, "not a compile-time constant")
    return 0.0
}

// Convert op= operators to expressions containing an assignment.
//
// In general, `A op= C` is converted to ``tmp = &A, *tmp = *tmp op B`.
// However, if a given expression is of form `A.x op= C`, the input is
// converted to `tmp = &A, (*tmp).x = (*tmp).x op C` to handle assignments
// to bitfields.
func toAssign(binary *Node) *Node {
    AddType(binary.lhs)
    AddType(binary.rhs)
    tok := binary.tok

    // Convert `A.x op= C` to `tmp = &A, (*tmp).x = (*tmp).x op C`.
    if binary.lhs.kind == ND_MEMBER {
        varObj := newLvar("", PointerTo(binary.lhs.lhs.ty))
        expr1 := 
            newBinary(
                ND_ASSIGN, 
                newVarNode(varObj, tok),
                newUnary(ND_ADDR, binary.lhs.lhs, tok), 
                tok)
        expr2 := 
            newUnary(
                ND_MEMBER,
                newUnary(ND_DEREF, newVarNode(varObj, tok), tok),
                tok)
        expr2.member = binary.lhs.member
        expr3 := 
            newUnary(
                ND_MEMBER,
                newUnary(ND_DEREF, newVarNode(varObj, tok), tok),
                tok)
        expr3.member = binary.lhs.member
        expr4 := 
            newBinary(
                ND_ASSIGN, 
                expr2,
                newBinary(binary.kind, expr3, binary.rhs, tok),
                tok)

        return newBinary(ND_COMMA, expr1, expr4, tok)
    }

    // If A is an atomic type, Convert `A op= B` to
    //
    // ({
    //   T1 *addr = &A; T2 val = (B); T1 old = *addr; T1 new;
    //   do {
    //    new = old op val;
    //   } while (!atomic_compare_exchange_strong(addr, &old, new));
    //   new;
    // })
    if binary.lhs.ty.isAtomic {
        var head Node
        cur := &head

        addr := newLvar("", PointerTo(binary.lhs.ty))
        val := newLvar("", binary.rhs.ty)
        oldVal := newLvar("", binary.lhs.ty)
        newVal := newLvar("", binary.lhs.ty)

        cur.next =
            newUnary(
                ND_EXPR_STMT,
                newBinary(
                    ND_ASSIGN, 
                    newVarNode(addr, tok),
                    newUnary(ND_ADDR, binary.lhs, tok), 
                    tok),
                tok)
        cur = cur.next

        cur.next =
            newUnary(
                ND_EXPR_STMT,
                newBinary(
                    ND_ASSIGN, 
                    newVarNode(val, tok), 
                    binary.rhs, 
                    tok),
                tok)
        cur = cur.next

        cur.next =
            newUnary(
                ND_EXPR_STMT,
                newBinary(
                    ND_ASSIGN, 
                    newVarNode(oldVal, tok),
                    newUnary(ND_DEREF, newVarNode(addr, tok), tok), 
                    tok),
                tok)
        cur = cur.next

        loop := newNode(ND_DO, tok)
        loop.brkLabel = newUniqueName()
        loop.contLabel = newUniqueName()

        body := 
            newBinary(
                ND_ASSIGN,
                newVarNode(newVal, tok),
                newBinary(
                    binary.kind, 
                    newVarNode(oldVal, tok),
                    newVarNode(val, tok), 
                    tok),
                tok)

        loop.then = newNode(ND_BLOCK, tok)
        loop.then.body = newUnary(ND_EXPR_STMT, body, tok)

        cas := newNode(ND_CAS, tok)
        cas.casAddr = newVarNode(addr, tok)
        cas.casOld = newUnary(ND_ADDR, newVarNode(oldVal, tok), tok)
        cas.casNew = newVarNode(newVal, tok)
        loop.cond = newUnary(ND_NOT, cas, tok)

        cur.next = loop
        cur = cur.next
        cur.next = newUnary(ND_EXPR_STMT, newVarNode(newVal, tok), tok)
        cur = cur.next

        node := newNode(ND_STMT_EXPR, tok)
        node.body = head.next
        return node
    }

    // Convert `A op= B` to ``tmp = &A, *tmp = *tmp op B`.
    varObj := newLvar("", PointerTo(binary.lhs.ty))
    expr1 := 
        newBinary(
            ND_ASSIGN, 
            newVarNode(varObj, tok),
            newUnary(ND_ADDR, binary.lhs, tok), 
            tok)
    expr2 :=
        newBinary(
            ND_ASSIGN,
            newUnary(ND_DEREF, newVarNode(varObj, tok), tok),
            newBinary(
                binary.kind,
                newUnary(ND_DEREF, newVarNode(varObj, tok), tok),
                binary.rhs,
                tok),
            tok)
    return newBinary(ND_COMMA, expr1, expr2, tok)
}

// assign    = conditional (assign-op assign)?
// assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^="
//           | "<<=" | ">>="
func assign(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = conditional(tok)

    if Equal(tok, "=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = newBinary(ND_ASSIGN, node, node2, tok)
        return
    }

    if Equal(tok, "+=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newAdd(node, node2, tok))
        return
    }

    if Equal(tok, "-=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newSub(node, node2, tok))
        return
    }

    if Equal(tok, "*=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_MUL, node, node2, tok))
        return
    }

    if Equal(tok, "/=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_DIV, node, node2, tok))
        return
    }

    if Equal(tok, "%=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_MOD, node, node2, tok))
        return
    }

    if Equal(tok, "&=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_BITAND, node, node2, tok))
        return
    }

    if Equal(tok, "|=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_BITOR, node, node2, tok))
        return
    }

    if Equal(tok, "^=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_BITXOR, node, node2, tok))
        return
    }

    if Equal(tok, "<<=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_SHL, node, node2, tok))
        return
    }

    if Equal(tok, ">>=") {
        var node2 *Node
        rest, node2 = assign(tok.next)
        out = toAssign(newBinary(ND_SHR, node, node2, tok))
        return
    }

    rest = tok
    out = node
    return
}

// conditional = logor ("?" expr? ":" conditional)?
func conditional(tok *Token) (rest *Token, out *Node) {
    var cond *Node
    tok, cond = logor(tok)

    if !Equal(tok, "?") {
        rest = tok
        out = cond
        return
  }

    if Equal(tok.next, ":") {
        // [GNU] Compile `a ?: b` as `tmp = a, tmp ? tmp : b`.
        AddType(cond)
        varObj := newLvar("", cond.ty)
        lhs := newBinary(ND_ASSIGN, newVarNode(varObj, tok), cond, tok)
        rhs := newNode(ND_COND, tok)
        rhs.cond = newVarNode(varObj, tok)
        rhs.then = newVarNode(varObj, tok)
        rest, rhs.els = conditional(tok.next.next)
        out = newBinary(ND_COMMA, lhs, rhs, tok)
        return
    }

    node := newNode(ND_COND, tok)
    node.cond = cond
    tok, node.then = expr(tok.next)
    tok = Skip(tok, ":")
    rest, node.els = conditional(tok)
    out = node
    return
}

// logor = logand ("||" logand)*
func logor(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = logand(tok)
    for Equal(tok, "||") {
        start := tok
        var node2 *Node
        tok, node2 = logand(tok.next)
        node = newBinary(ND_LOGOR, node, node2, start)
    }
    rest = tok
    out = node
    return
}

// logand = bitor ("&&" bitor)*
func logand(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = bitor(tok)
    for Equal(tok, "&&") {
        start := tok
        var node2 *Node
        tok, node2 = bitor(tok.next)
        node = newBinary(ND_LOGAND, node, node2, start)
    }
    rest = tok
    out = node
    return
}

// bitor = bitxor ("|" bitxor)*
func bitor(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = bitxor(tok)
    for Equal(tok, "|") {
        start := tok
        var node2 *Node
        tok, node2 = bitxor(tok.next)
        node = newBinary(ND_BITOR, node, node2, start)
    }
    rest = tok
    out = node
    return
}

// bitxor = bitand ("^" bitand)*
func bitxor(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = bitand(tok)
    for Equal(tok, "^") {
        start := tok
        var node2 *Node
        tok, node2 = bitand(tok.next)
        node = newBinary(ND_BITXOR, node, node2, start)
    }
    rest = tok
    out = node
    return
}

// bitand = equality ("&" equality)*
func bitand(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = equality(tok)
    for Equal(tok, "&") {
        start := tok
        var node2 *Node
        tok, node2 = equality(tok.next)
        node = newBinary(ND_BITAND, node, node2, start)
    }
    rest = tok
    out = node
    return
}

// equality = relational ("==" relational | "!=" relational)*
func equality(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = relational(tok)

    for {
        start := tok

        if Equal(tok, "==") {
            var node2 *Node
            tok, node2 = relational(tok.next)
            node = newBinary(ND_EQ, node, node2, start)
            continue
        }

        if Equal(tok, "!=") {
            var node2 *Node
            tok, node2 = relational(tok.next)
            node = newBinary(ND_NE, node, node2, start)
            continue
        }

        rest = tok
        out = node
        return
    }
}

// relational = shift ("<" shift | "<=" shift | ">" shift | ">=" shift)*
func relational(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = shift(tok)

    for {
        start := tok

        if Equal(tok, "<") {
            var node2 *Node
            tok, node2 = shift(tok.next)
            node = newBinary(ND_LT, node, node2, start)
            continue
        }

        if Equal(tok, "<=") {
            var node2 *Node
            tok, node2 = shift(tok.next)
            node = newBinary(ND_LE, node, node2, start)
            continue
        }

        if Equal(tok, ">") {
            var node2 *Node
            tok, node2 = shift(tok.next)
            node = newBinary(ND_LT, node2, node, start)
            continue
        }

        if Equal(tok, ">=") {
            var node2 *Node
            tok, node2 = shift(tok.next)
            node = newBinary(ND_LE, node2, node, start)
            continue
        }

        rest = tok
        out = node
        return
    }
}

// shift = add ("<<" add | ">>" add)*
func shift(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = add(tok)

    for {
        start := tok

        if Equal(tok, "<<") {
            var node2 *Node
            tok, node2 = add(tok.next)
            node = newBinary(ND_SHL, node, node2, start)
            continue
        }

        if Equal(tok, ">>") {
            var node2 *Node
            tok, node2 = add(tok.next)
            node = newBinary(ND_SHR, node, node2, start)
            continue
        }

        rest = tok
        out = node
        return
  }
}

// In C, `+` operator is overloaded to perform the pointer arithmetic.
// If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
// so that p+n points to the location n elements (not bytes) ahead of p.
// In other words, we need to scale an integer value before adding to a
// pointer value. This function takes care of the scaling.
func newAdd(lhs *Node, rhs *Node, tok *Token) *Node {
    AddType(lhs)
    AddType(rhs)

    // num + num
    if IsNumeric(lhs.ty) && IsNumeric(rhs.ty) {
        return newBinary(ND_ADD, lhs, rhs, tok)
    }

    if lhs.ty.base != nil && rhs.ty.base != nil {
        ErrorTok(tok, "invalid operands")
    }

    // Canonicalize `num + ptr` to `ptr + num`.
    if lhs.ty.base == nil && rhs.ty.base != nil {
        lhs, rhs = rhs, lhs
    }

    // VLA + num
    if lhs.ty.base.kind == TY_VLA {
        rhs = newBinary(ND_MUL, rhs, newVarNode(lhs.ty.base.vlaSize, tok), tok)
        return newBinary(ND_ADD, lhs, rhs, tok)
    }

    // ptr + num
    rhs = newBinary(ND_MUL, rhs, newLong(int64(lhs.ty.base.size), tok), tok)
    return newBinary(ND_ADD, lhs, rhs, tok)
}

// Like `+`, `-` is overloaded for the pointer type.
func newSub(lhs *Node, rhs *Node, tok *Token) *Node {
    AddType(lhs)
    AddType(rhs)

    // num - num
    if IsNumeric(lhs.ty) && IsNumeric(rhs.ty) {
        return newBinary(ND_SUB, lhs, rhs, tok)
    }

    // VLA + num
    if lhs.ty.base.kind == TY_VLA {
        rhs = newBinary(ND_MUL, rhs, newVarNode(lhs.ty.base.vlaSize, tok), tok)
        AddType(rhs)
        node := newBinary(ND_SUB, lhs, rhs, tok)
        node.ty = lhs.ty
        return node
    }

    // ptr - num
    if lhs.ty.base != nil && IsInteger(rhs.ty) {
        rhs = newBinary(ND_MUL, rhs, newLong(int64(lhs.ty.base.size), tok), tok)
        AddType(rhs)
        node := newBinary(ND_SUB, lhs, rhs, tok)
        node.ty = lhs.ty
        return node
    }

    // ptr - ptr, which returns how many elements are between the two.
    if lhs.ty.base != nil && rhs.ty.base != nil {
        node := newBinary(ND_SUB, lhs, rhs, tok)
        node.ty = TyLong
        return newBinary(ND_DIV, node, newNum(int64(lhs.ty.base.size), tok), tok)
    }

    ErrorTok(tok, "invalid operands")
    return nil
}

// add = mul ("+" mul | "-" mul)*
func add(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = mul(tok)

    for {
        start := tok

        if Equal(tok, "+") {
            var node2 *Node
            tok, node2 = mul(tok.next)
            node = newAdd(node, node2, start)
            continue
        }

        if Equal(tok, "-") {
            var node2 *Node
            tok, node2 = mul(tok.next)
            node = newSub(node, node2, start)
            continue
        }

        rest = tok
        out = node
        return
    }
}

// mul = cast ("*" cast | "/" cast | "%" cast)*
func mul(tok *Token) (rest *Token, out *Node) {
    var node *Node
    tok, node = cast(tok)

    for {
        start := tok

        if Equal(tok, "*") {
            var node2 *Node
            tok, node2 = cast(tok.next)
            node = newBinary(ND_MUL, node, node2, start)
            continue
        }

        if Equal(tok, "/") {
            var node2 *Node
            tok, node2 = cast(tok.next)
            node = newBinary(ND_DIV, node, node2, start)
            continue
        }

        if Equal(tok, "%") {
            var node2 *Node
            tok, node2 = cast(tok.next)
            node = newBinary(ND_MOD, node, node2, start)
            continue
        }

        rest = tok
        out = node
        return
    }
}

// cast = "(" type-name ")" cast | unary
func cast(tok *Token) (rest *Token, out *Node) {
    if Equal(tok, "(") && isTypename(tok.next) {
        start := tok
        tok, ty := typename(tok.next)
        tok = Skip(tok, ")")

        // compound literal
        if Equal(tok, "{") {
            rest, out = unary(start)
            return
        }

        // type cast
        var node *Node
        rest, node = cast(tok)
        node = NewCast(node, ty)
        node.tok = start
        out = node
        return
    }

    rest, out = unary(tok)
    return
}

// unary = ("+" | "-" | "*" | "&" | "!" | "~") cast
//       | ("++" | "--") unary
//       | "&&" ident
//       | postfix
func unary(tok *Token) (rest *Token, out *Node) {
    if Equal(tok, "+") {
        rest, out = cast(tok.next)
        return
    }

    if Equal(tok, "-") {
        var node *Node
        rest, node = cast(tok.next)
        out = newUnary(ND_NEG, node, tok)
        return
    }

    if Equal(tok, "&") {
        var node *Node
        rest, node = cast(tok.next)
        AddType(node)
        if node.kind == ND_MEMBER && node.member.isBitfield {
            ErrorTok(tok, "cannot take address of bitfield")
        }
        out = newUnary(ND_ADDR, node, tok)
        return
    }

    if Equal(tok, "*") {
        // [https://www.sigbus.info/n1570#6.5.3.2p4] This is an oddity
        // in the C spec, but dereferencing a function shouldn't do
        // anything. If foo is a function, `*foo`, `**foo` or `*****foo`
        // are all equivalent to just `foo`.
        var node *Node
        rest, node = cast(tok.next)
        AddType(node)
        if node.ty.kind == TY_FUNC {
            out = node
            return
        }
        out = newUnary(ND_DEREF, node, tok)
        return
    }

    if Equal(tok, "!") {
        var node *Node
        rest, node = cast(tok.next)
        out = newUnary(ND_NOT, node, tok)
        return
    }

    if Equal(tok, "~") {
        var node *Node
        rest, node = cast(tok.next)
        out = newUnary(ND_BITNOT, node, tok)
        return
    }

    // Read ++i as i+=1
    if Equal(tok, "++") {
        var node *Node
        rest, node = unary(tok.next)
        out = toAssign(newAdd(node, newNum(1, tok), tok))
        return
    }

    // Read --i as i-=1
    if Equal(tok, "--") {
        var node *Node
        rest, node = unary(tok.next)
        out = toAssign(newSub(node, newNum(1, tok), tok))
        return
    }

    // [GNU] labels-as-values
    if Equal(tok, "&&") {
        node := newNode(ND_LABEL_VAL, tok)
        node.label = getIdent(tok.next)
        node.gotoNext = gotos
        gotos = node
        rest = tok.next.next
        out = node
        return
    }

    rest, out = postfix(tok)
    return
}

// struct-members = (declspec declarator (","  declarator)* ";")*
func structMembers(tok *Token, ty *Type) *Token {
    var head Member
    cur := &head
    idx := 0

    for !Equal(tok, "}") {
        var attr VarAttr
        var basety *Type
        tok, basety = declspec(tok, &attr)
        first := true

        // Anonymous struct member
        if basety.kind == TY_STRUCT || basety.kind == TY_UNION {
            var anon bool
            tok, anon = Consume(tok, ";")
            if anon {
                mem := new(Member)
                mem.ty = basety
                mem.idx = idx
                idx++
                if attr.align != 0 {
                    mem.align = attr.align
                } else {
                    mem.align = mem.ty.align
                }
                cur.next = mem
                cur = cur.next
                continue
            }
        }

        // Regular struct members
        for {
            var done bool
            tok, done = Consume(tok, ";")
            if done {
                break
            }

            if !first {
                tok = Skip(tok, ",")
            }
            first = false

            mem := new(Member)
            tok, mem.ty = declarator(tok, basety)
            mem.name = mem.ty.name
            mem.idx = idx
            idx++
            if attr.align != 0 {
                mem.align = attr.align
            } else {
                mem.align = mem.ty.align
            }

            var bit bool
            tok, bit = Consume(tok, ":")
            if bit {
                mem.isBitfield = true
                var val int64
                tok, val = ConstExpr(tok)
                mem.bitWidth = int(val)
            }

            cur.next = mem
            cur = cur.next
        }
    }

    // If the last element is an array of incomplete type, it's
    // called a "flexible array member". It should behave as if
    // if were a zero-sized array.
    if cur != &head && cur.ty.kind == TY_ARRAY && cur.ty.arrayLen < 0 {
        cur.ty = ArrayOf(cur.ty.base, 0)
        ty.isFlexible = true
    }

    ty.members = head.next
    return tok.next
}

// attribute = ("__attribute__" "(" "(" "packed" ")" ")")*
func attributeList(tok *Token, ty *Type) *Token {
    for {
        var attr bool
        tok, attr = Consume(tok, "__attribute__")
        if !attr {
            break
        }

        tok = Skip(tok, "(")
        tok = Skip(tok, "(")

        first := true

        for {
            var done bool
            tok, done = Consume(tok, ")")
            if done {
                break
            }

            if !first {
                tok = Skip(tok, ",")
            }
            first = false

            var packed bool
            tok, packed = Consume(tok, "packed")
            if packed {
                ty.isPacked = true
                continue
            }

            var aligned bool
            tok, aligned = Consume(tok, "aligned")
            if aligned {
                tok = Skip(tok, "(")
                var val int64
                tok, val = ConstExpr(tok)
                ty.align = int(val)
                tok = Skip(tok, ")")
                continue
            }

            ErrorTok(tok, "unknown attribute")
        }

        tok = Skip(tok, ")")
    }

    return tok
}

// struct-union-decl = attribute? ident? ("{" struct-members)?
func structUnionDecl(tok *Token) (rest *Token, out *Type) {
    ty := StructType()
    tok = attributeList(tok, ty)

    // Read a tag.
    var tag *Token
    if tok.kind == TK_IDENT {
        tag = tok
        tok = tok.next
    }

    if tag != nil && !Equal(tok, "{") {
        rest = tok

        ty2 := findTag(tag)
        if ty2 != nil {
            out = ty2
            return
        }

        ty.size = -1
        pushTagScope(tag, ty)
        out = ty
        return
    }

    tok = Skip(tok, "{")

    // Construct a struct object.
    tok = structMembers(tok, ty)
    rest = attributeList(tok, ty)

    if tag != nil {
        // If this is a redefinition, overwrite a previous type.
        // Otherwise, register the struct type.
        ty2, ok := scope.tags[string(tag.text)]
        if ok {
            *ty2 = *ty
            out = ty2
            return
        }

        pushTagScope(tag, ty)
    }

    out = ty
    return
}

// struct-decl = struct-union-decl
func structDecl(tok *Token) (rest *Token, out *Type) {
    var ty *Type
    rest, ty = structUnionDecl(tok)
    ty.kind = TY_STRUCT

    if ty.size < 0 {
        out = ty
        return
    }

    // Assign offsets within the struct to members.
    bits := 0

    for mem := ty.members; mem != nil; mem = mem.next {
        switch {
        case mem.isBitfield && mem.bitWidth == 0:
            // Zero-width anonymous bitfield has a special meaning.
            // It affects only alignment.
            bits = AlignTo(bits, mem.ty.size*8)
        case mem.isBitfield:
            sz := mem.ty.size
            if bits / (sz * 8) != (bits + mem.bitWidth - 1) / (sz * 8) {
                bits = AlignTo(bits, sz*8)
            }
            mem.offset = alignDown(bits/8, sz)
            mem.bitOffset = bits % (sz * 8)
            bits += mem.bitWidth
        default:
            if !ty.isPacked {
                bits = AlignTo(bits, mem.align*8)
            }
            mem.offset = bits / 8
            bits += mem.ty.size * 8
        }

        if !ty.isPacked && ty.align < mem.align {
            ty.align = mem.align
        }
    }

    ty.size = AlignTo(bits, ty.align * 8) / 8
    out = ty
    return
}

func unionDecl(tok *Token) (rest *Token, out *Type) {
    var ty *Type
    rest, ty = structUnionDecl(tok)
    ty.kind = TY_UNION

    if ty.size < 0 {
        out = ty
        return
    }

    // If union, we don't have to assign offsets because they
    // are already initialized to zero. We need to compute the
    // alignment and the size though.
    for mem := ty.members; mem != nil; mem = mem.next {
        if ty.align < mem.align {
            ty.align = mem.align
        }
        if ty.size < mem.ty.size {
            ty.size = mem.ty.size
        }
    }
    ty.size = AlignTo(ty.size, ty.align)
    out = ty
    return
}

// Find a struct member by name.
func getStructMember(ty *Type, tok *Token) *Member {
    for mem := ty.members; mem != nil; mem = mem.next {
        // Anonymous struct member
        if (mem.ty.kind == TY_STRUCT || mem.ty.kind == TY_UNION) && mem.name == nil {
            if getStructMember(mem.ty, tok) != nil {
                return mem
            }
            continue
        }
        // Regular struct member
        if string(mem.name.text) == string(tok.text) {
            return mem
        }
    }
    return nil
}

// Create a node representing a struct member access, such as foo.bar
// where foo is a struct and bar is a member name.
//
// C has a feature called "anonymous struct" which allows a struct to
// have another unnamed struct as a member like this:
//
//   struct { struct { int a; }; int b; } x;
//
// The members of an anonymous struct belong to the outer struct's
// member namespace. Therefore, in the above example, you can access
// member "a" of the anonymous struct as "x.a".
//
// This function takes care of anonymous structs.
func structRef(node *Node, tok *Token) *Node {
    AddType(node)

    if node.ty.kind != TY_STRUCT && node.ty.kind != TY_UNION {
        ErrorTok(node.tok, "not a struct nor a union")
    }

    ty := node.ty

    for {
        mem := getStructMember(ty, tok)
        if mem == nil {
            ErrorTok(tok, "no such member")
        }
        node = newUnary(ND_MEMBER, node, tok)
        node.member = mem
        if mem.name != nil {
            break
        }
        ty = mem.ty
    }
    return node
}

// Convert A++ to `(typeof A)((A += 1) - 1)`
func newIncDec(node *Node, tok *Token, addend int) *Node {
    AddType(node)
    return NewCast(
        newAdd(
            toAssign(newAdd(node, newNum(int64(addend), tok), tok)),
            newNum(int64(-addend), tok), 
            tok),
        node.ty)
}

// postfix = "(" type-name ")" "{" initializer-list "}"
//         = ident "(" func-args ")" postfix-tail*
//         | primary postfix-tail*
//
// postfix-tail = "[" expr "]"
//              | "(" func-args ")"
//              | "." ident
//              | "->" ident
//              | "++"
//              | "--"
func postfix(tok *Token) (rest *Token, out *Node) {
    if Equal(tok, "(") && isTypename(tok.next) {
        // Compound literal
        start := tok
        var ty *Type
        tok, ty = typename(tok.next)
        tok = Skip(tok, ")")

        if scope.next == nil {
            varObj := newAnonGvar(ty)
            rest = gvarInitializer(tok, varObj)
            out = newVarNode(varObj, start)
            return
        }

        varObj := newLvar("", ty)
        var lhs *Node
        rest, lhs = lvarInitializer(tok, varObj)
        rhs := newVarNode(varObj, tok)
        out = newBinary(ND_COMMA, lhs, rhs, start)
        return
    }

    var node *Node
    tok, node = primary(tok)

    for {
        if Equal(tok, "(") {
            tok, node = funcall(tok.next, node)
            continue
        }

        if Equal(tok, "[") {
            // x[y] is short for *(x+y)
            start := tok
            var idx *Node
            tok, idx = expr(tok.next)
            tok = Skip(tok, "]")
            node = newUnary(ND_DEREF, newAdd(node, idx, start), start)
            continue
        }

        if Equal(tok, ".") {
            node = structRef(node, tok.next)
            tok = tok.next.next
            continue
        }

        if Equal(tok, "->") {
            // x->y is short for (*x).y
            node = newUnary(ND_DEREF, node, tok)
            node = structRef(node, tok.next)
            tok = tok.next.next
            continue
        }

        if Equal(tok, "++") {
            node = newIncDec(node, tok, 1)
            tok = tok.next
            continue
        }

        if Equal(tok, "--") {
            node = newIncDec(node, tok, -1)
            tok = tok.next
            continue
        }

        rest = tok
        out = node
        return
    }
}

// funcall = (assign ("," assign)*)? ")"
func funcall(tok *Token, fn *Node) (rest *Token, out *Node) {
    AddType(fn)

    if fn.ty.kind != TY_FUNC &&
            (fn.ty.kind != TY_PTR || fn.ty.base.kind != TY_FUNC) {
        ErrorTok(fn.tok, "not a function")
    }

    var ty *Type
    if fn.ty.kind == TY_FUNC {
        ty = fn.ty
    } else {
        ty = fn.ty.base
    }
    paramTy := ty.params

    var head Node
    cur := &head

    for !Equal(tok, ")") {
        if cur != &head {
            tok = Skip(tok, ",")
        }

        var arg *Node
        tok, arg = assign(tok)
        AddType(arg)

        if paramTy == nil && !ty.isVariadic {
            ErrorTok(tok, "too many arguments")
        }

        switch {
        case paramTy != nil:
            if paramTy.kind != TY_STRUCT && paramTy.kind != TY_UNION {
                arg = NewCast(arg, paramTy)
            }
            paramTy = paramTy.next
        case arg.ty.kind == TY_FLOAT:
            // If parameter type is omitted (e.g. in "..."), float
            // arguments are promoted to double.
            arg = NewCast(arg, TyDouble)
        }

        cur.next = arg
        cur = cur.next
    }

    if paramTy != nil {
        ErrorTok(tok, "too few arguments")
    }

    rest = Skip(tok, ")")

    node := newUnary(ND_FUNCALL, fn, tok)
    node.funcTy = ty
    node.ty = ty.returnTy
    node.args = head.next

    // If a function returns a struct, it is caller's responsibility
    // to allocate a space for the return value.
    if node.ty.kind == TY_STRUCT || node.ty.kind == TY_UNION {
        node.retBuffer = newLvar("", node.ty)
    }

    out = node
    return
}

// generic-selection = "(" assign "," generic-assoc ("," generic-assoc)* ")"
//
// generic-assoc = type-name ":" assign
//               | "default" ":" assign
func genericSelection(tok *Token) (rest *Token, out *Node) {
    start := tok
    tok = Skip(tok, "(")

    var ctrl *Node
    tok, ctrl = assign(tok)
    AddType(ctrl)

    t1 := ctrl.ty
    switch t1.kind {
    case TY_FUNC:
        t1 = PointerTo(t1)
    case TY_ARRAY:
        t1 = PointerTo(t1.base)
    }

    var ret *Node

    for {
        var done bool
        rest, done = Consume(tok, ")")
        if done {
            break
        }

        tok = Skip(tok, ",")

        if Equal(tok, "default") {
            tok = Skip(tok.next, ":")
            var node *Node
            tok, node = assign(tok)
            if ret == nil {
                ret = node
            }
            continue
        }

        var t2 *Type
        tok, t2 = typename(tok)
        tok = Skip(tok, ":")
        var node *Node
        tok, node = assign(tok)
        if IsCompatible(t1, t2) {
            ret = node
        }
    }

    if ret == nil {
        ErrorTok(start, 
            "controlling expression type not compatible with"+
            " any generic association type")
    }

    out = ret
    return
}

// primary = "(" "{" stmt+ "}" ")"
//         | "(" expr ")"
//         | "sizeof" "(" type-name ")"
//         | "sizeof" unary
//         | "_Alignof" "(" type-name ")"
//         | "_Alignof" unary
//         | "_Generic" generic-selection
//         | "__builtin_types_compatible_p" "(" type-name, type-name, ")"
//         | "__builtin_reg_class" "(" type-name ")"
//         | ident
//         | str
//         | num
func primary(tok *Token) (rest *Token, out *Node) {
    start := tok

    if Equal(tok, "(") && Equal(tok.next, "{") {
        // This is a GNU statement expresssion.
        node := newNode(ND_STMT_EXPR, tok)
        var node2 *Node
        tok, node2 = compoundStmt(tok.next.next)
        node.body = node2.body
        rest = Skip(tok, ")")
        out = node
        return
    }

    if Equal(tok, "(") {
        var node *Node
        tok, node = expr(tok.next)
        rest = Skip(tok, ")")
        out = node
        return
    }

    if Equal(tok, "sizeof") && Equal(tok.next, "(") && isTypename(tok.next.next) {
        var ty *Type
        tok, ty = typename(tok.next.next)
        rest = Skip(tok, ")")

        if ty.kind == TY_VLA {
            if ty.vlaSize != nil {
                out = newVarNode(ty.vlaSize, tok)
                return
            }

            lhs := computeVlaSize(ty, tok)
            rhs := newVarNode(ty.vlaSize, tok)
            out = newBinary(ND_COMMA, lhs, rhs, tok)
            return
        }

        out = newUlong(int64(ty.size), start)
        return
    }

    if Equal(tok, "sizeof") {
        var node *Node
        rest, node = unary(tok.next)
        AddType(node)
        if node.ty.kind == TY_VLA {
            out = newVarNode(node.ty.vlaSize, tok)
            return
        }
        out = newUlong(int64(node.ty.size), tok)
        return
    }

    if Equal(tok, "_Alignof") && Equal(tok.next, "(") && isTypename(tok.next.next) {
        var ty *Type
        tok, ty = typename(tok.next.next)
        rest = Skip(tok, ")")
        out = newUlong(int64(ty.align), tok)
        return
    }

    if Equal(tok, "_Alignof") {
        var node *Node
        rest, node = unary(tok.next)
        AddType(node)
        out = newUlong(int64(node.ty.align), tok)
        return
    }

    if Equal(tok, "_Generic") {
        rest, out = genericSelection(tok.next)
        return
    }

    if Equal(tok, "__builtin_types_compatible_p") {
        tok = Skip(tok.next, "(")
        var t1 *Type
        tok, t1 = typename(tok)
        tok = Skip(tok, ",")
        var t2 *Type
        tok, t2 = typename(tok)
        rest = Skip(tok, ")")
        var val int64
        if IsCompatible(t1, t2) {
            val = 1
        } else {
            val = 2
        }
        out = newNum(val, start)
        return
    }

    if Equal(tok, "__builtin_reg_class") {
        tok = Skip(tok.next, "(")
        var ty *Type
        tok, ty = typename(tok)
        rest = Skip(tok, ")")

        if IsInteger(ty) || ty.kind == TY_PTR {
            out = newNum(0, start)
            return
        }
        if IsFlonum(ty) {
            out = newNum(1, start)
            return
        }
        out = newNum(2, start)
        return
    }

    if Equal(tok, "__builtin_compare_and_swap") {
        node := newNode(ND_CAS, tok)
        tok = Skip(tok.next, "(")
        tok, node.casAddr = assign(tok)
        tok = Skip(tok, ",")
        tok, node.casOld = assign(tok)
        tok = Skip(tok, ",")
        tok, node.casNew = assign(tok)
        rest = Skip(tok, ")")
        out = node
        return
    }

    if Equal(tok, "__builtin_atomic_exchange") {
        node := newNode(ND_EXCH, tok)
        tok = Skip(tok.next, "(")
        tok, node.lhs = assign(tok)
        tok = Skip(tok, ",")
        tok, node.rhs = assign(tok)
        rest = Skip(tok, ")")
        out = node
        return
    }

    if tok.kind == TK_IDENT {
        // Variable or enum constant
        sc := findVar(tok)
        rest = tok.next

        // For "static inline" function
        if sc != nil && sc.varObj != nil && sc.varObj.isFunction {
            if currentFn != nil {
                currentFn.refs = append(currentFn.refs, sc.varObj.name)
            } else {
                sc.varObj.isRoot = true
            }
        }

        if sc != nil {
            if sc.varObj != nil {
                out = newVarNode(sc.varObj, tok)
                return
            }
            if sc.enumTy != nil {
                out = newNum(int64(sc.enumVal), tok)
                return
            }
        }

        if Equal(tok.next, "(") {
            ErrorTok(tok, "implicit declaration of a function")
        }
        ErrorTok(tok, "undefined variable")
    }

    if tok.kind == TK_STR {
        varObj := newStringLiteral(tok.str, tok.ty)
        rest = tok.next
        out = newVarNode(varObj, tok)
        return
    }

    if tok.kind == TK_NUM {
        var node *Node
        if IsFlonum(tok.ty) {
            node = newNode(ND_NUM, tok)
            node.fval = tok.fval
        } else {
            node = newNum(tok.val, tok)
        }

        node.ty = tok.ty
        rest = tok.next
        out = node
        return
    }

    ErrorTok(tok, "expected an expression")
    return
}

func parseTypedef(tok *Token, basety *Type) *Token {
    first := true

    for {
        var done bool
        tok, done = Consume(tok, ";")
        if done {
            break
        }

        if !first {
            tok = Skip(tok, ",")
        }
        first = false

        var ty *Type
        tok, ty = declarator(tok, basety)
        if ty.name == nil {
            ErrorTok(ty.namePos, "typedef name omitted")
        }
        sc := pushScope(getIdent(ty.name))
        sc.typeDef = ty
    }
    return tok
}

func createParamLvars(param *Type) {
    if param != nil {
        createParamLvars(param.next)
        if param.name == nil {
            ErrorTok(param.namePos, "parameter name omitted")
        }
        newLvar(getIdent(param.name), param)
    }
}

// This function matches gotos or labels-as-values with labels.
//
// We cannot resolve gotos as we parse a function because gotos
// can refer a label that appears later in the function.
// So, we need to do this after we parse the entire function.
func resolveGotoLabels() {
    for x := gotos; x != nil; x = x.gotoNext {
        for y := labels; y != nil; y = y.gotoNext {
            if x.label == y.label {
                x.uniqueLabel = y.uniqueLabel
                break
            }
        }

        if len(x.uniqueLabel) == 0 {
            ErrorTok(x.tok.next, "use of undeclared label")
        }
    }

    gotos = nil
    labels = nil
}

func findFunc(name string) *Obj {
    sc := scope
    for sc.next != nil {
        sc = sc.next
    }

    sc2, ok := sc.vars[name]
    if ok && sc2.varObj != nil && sc2.varObj.isFunction {
        return sc2.varObj
    }

    return nil
}

func markLive(varObj *Obj) {
    if !varObj.isFunction || varObj.isLive {
        return
    }
    varObj.isLive = true

    for _, ref := range varObj.refs {
        fn := findFunc(ref)
        if fn != nil {
            markLive(fn)
        }
    }
}

func function(tok *Token, basety *Type, attr *VarAttr) *Token {
    var ty *Type
    tok, ty = declarator(tok, basety)
    if ty.name == nil {
        ErrorTok(ty.namePos, "function name omitted")
    }
    nameStr := getIdent(ty.name)

    fn := findFunc(nameStr)
    if fn != nil {
        // Redeclaration
        if !fn.isFunction {
            ErrorTok(tok, "redeclared as a different kind of symbol")
        }
        if fn.isDefinition && Equal(tok, "{") {
            ErrorTok(tok, "redefinition of %s", nameStr)
        }
        if !fn.isStatic && attr.isStatic {
            ErrorTok(tok, "static declaration follows a non-static declaration")
        }
        fn.isDefinition = (fn.isDefinition || Equal(tok, "{"))
    } else {
        fn = newGvar(nameStr, ty)
        fn.isFunction = true
        fn.isDefinition = Equal(tok, "{")
        fn.isStatic = (attr.isStatic || (attr.isInline && !attr.isExtern))
        fn.isInline = attr.isInline
    }

    fn.isRoot = !(fn.isStatic && fn.isInline)

    var done bool
    tok, done = Consume(tok, ";")
    if done {
        return tok
    }

    currentFn = fn
    locals = nil
    enterScope()
    createParamLvars(ty.params)

    // A buffer for a struct/union return value is passed
    // as the hidden first parameter.
    rty := ty.returnTy
    if (rty.kind == TY_STRUCT || rty.kind == TY_UNION) && rty.size > 16 {
        newLvar("", PointerTo(rty))
    }

    fn.params = locals

    if ty.isVariadic {
        fn.vaArea = newLvar("__va_area__", ArrayOf(TyChar, 136))
    }
    fn.allocaBottom = newLvar("__alloca_size__", PointerTo(TyChar))

    tok = Skip(tok, "{")

    // [https://www.sigbus.info/n1570#6.4.2.2p1] "__func__" is
    // automatically defined as a local variable containing the
    // current function name.
    name := []byte(fn.name)
    name = append(name, 0)

    sc := pushScope("__func__")
    sc.varObj = newStringLiteral(name, ArrayOf(TyChar, len(name)))

    // [GNU] __FUNCTION__ is yet another name of __func__.
    sc = pushScope("__FUNCTION__")
    sc.varObj = newStringLiteral(name, ArrayOf(TyChar, len(name)))

    tok, fn.body = compoundStmt(tok)
    fn.locals = locals
    leaveScope()
    resolveGotoLabels()
    return tok
}

func globalVariable(tok *Token, basety *Type, attr *VarAttr) *Token {
    first := true

    for {
        var done bool
        tok, done = Consume(tok, ";")
        if done {
            break
        }

        if !first {
            tok = Skip(tok, ",")
        }
        first = false

        var ty *Type
        tok, ty = declarator(tok, basety)
        if ty.name == nil {
            ErrorTok(ty.namePos, "variable name omitted")
        }

        varObj := newGvar(getIdent(ty.name), ty)
        varObj.isDefinition = !attr.isExtern
        varObj.isStatic = attr.isStatic
        varObj.isTls = attr.isTls
        if attr.align != 0 {
            varObj.align = attr.align
        }

        switch {
        case Equal(tok, "="):
            tok = gvarInitializer(tok.next, varObj)
        case !attr.isExtern && !attr.isTls:
            varObj.isTentative = true
        }
    }

    return tok
}

// Lookahead tokens and returns true if a given token is a start
// of a function definition or declaration.
func isFunction(tok *Token) bool {
    if Equal(tok, ";") {
        return false
    }

    var dummy Type
    var ty *Type
    tok, ty = declarator(tok, &dummy)
    return (ty.kind == TY_FUNC)
}

// Removes redundant tentative definitions.
func scanGlobals() {
    var head Obj
    cur := &head

    for varObj := globals; varObj != nil; varObj = varObj.next {
        if !varObj.isTentative {
            cur.next = varObj
            cur = cur.next
            continue
        }

        // Find another definition of the same identifier.
        var2 := globals
        for ; var2 != nil; var2 = var2.next {
            if varObj != var2 && var2.isDefinition && varObj.name == var2.name {
                break
            }
        }

        // If there's another definition, the tentative definition
        // is redundant
        if var2 == nil {
            cur.next = varObj
            cur = cur.next
        }
    }

    cur.next = nil
    globals = head.next
}

func declareBuiltinFunctions() {
    ty := FuncType(PointerTo(TyVoid))
    ty.params = CopyType(TyInt)
    builtinAlloca = newGvar("alloca", ty)
    builtinAlloca.isDefinition = false
}

// program = (typedef | function-definition | global-variable)*
func Parse(tok *Token) *Obj {
    declareBuiltinFunctions()
    globals = nil

    for tok.kind != TK_EOF {
        var attr VarAttr
        var basety *Type
        tok, basety = declspec(tok, &attr)

        // Typedef
        if attr.isTypedef {
            tok = parseTypedef(tok, basety)
            continue
        }

        // Function
        if isFunction(tok) {
            tok = function(tok, basety, &attr)
            continue
        }

        // Global variable
        tok = globalVariable(tok, basety, &attr)
    }

    for varObj := globals; varObj != nil; varObj = varObj.next {
        if varObj.isRoot {
            markLive(varObj)
        }
    }

    // Remove redundant tentative definitions.
    scanGlobals()
    return globals
}

