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

// This file implements the C preprocessor.
//
// The preprocessor takes a list of tokens as an input and returns a
// new list of tokens as an output.
//
// The preprocessing language is designed in such a way that that's
// guaranteed to stop even if there is a recursive macro.
// Informally speaking, a macro is applied only once for each token.
// That is, if a macro token T appears in a result of direct or
// indirect macro expansion of T, T won't be expanded any further.
// For example, if T is defined as U, and U is defined as T, then
// token T is expanded to U and then to T and the macro expansion
// stops at that point.
//
// To achieve the above behavior, we attach for each token a set of
// macro names from which the token is expanded. The set is called
// "hideset". Hideset is initially empty, and every time we expand a
// macro, the macro name is added to the resulting tokens' hidesets.
//
// The above macro expansion algorithm is explained in this document
// written by Dave Prossor, which is used as a basis for the
// standard's wording:
// https://github.com/rui314/chibicc/wiki/cpp.algo.pdf 

package core

import (
    "fmt"
    "time"
)

//
//    MacroParam
//

type MacroParam struct {
    next *MacroParam
    name string
}

//
//    MacroArg
//

type MacroArg struct {
    next *MacroArg
    name string
    isVaArgs bool
    tok *Token
}

//
//    Macro
//

type MacroHandlerFn func(*Token) *Token

type Macro struct {
    name string
    isObjlike bool // Object-like or function-like
    params *MacroParam
    vaArgsName string
    body *Token
    handler MacroHandlerFn
}

//
//    CondIncl
//

// `#if` can be nested, so we use a stack to manage nested `#if`s.

type CondCtx int

const (
    IN_THEN CondCtx = iota
    IN_ELIF
    IN_ELSE
)

type CondIncl struct {
    next *CondIncl
    ctx CondCtx
    tok *Token
    included bool
}

//
//    Hideset
//

type Hideset struct {
    next *Hideset
    name string
}

//
//    Private state variables
//

var (
    macros map[string]*Macro
    condIncl *CondIncl
    pragmaOnce map[string]bool
    includeNextIdx int
    includeCache map[string]string
    includeGuards map[string]string
    counterNextIdx int
)

func init() {
    macros = make(map[string]*Macro)
    condIncl = nil
    pragmaOnce = make(map[string]bool)
    includeNextIdx = 0
    includeCache = make(map[string]string)
    includeGuards = make(map[string]string)
    counterNextIdx = 0
}

//
//    Private functions
//

func isHash(tok *Token) bool {
    return (tok.atBol && Equal(tok, "#"))
} 

// Some preprocessor directives such as #include allow extraneous
// tokens before newline. This function skips such tokens.
func skipLine(tok *Token) *Token {
    if (tok.atBol) {
        return tok
    }
    WarnTok(tok, "extra token")
    for tok.atBol {
        tok = tok.next
    }
    return tok
} 

func copyToken(tok *Token) *Token {
    t := new(Token)
    *t = *tok
    t.next = nil
    return t
}

func newEof(tok *Token) *Token {
    t := copyToken(tok)
    t.kind = TK_EOF
    return t
}

func newHideset(name string) *Hideset {
    hs := new(Hideset)
    hs.name = name
    return hs
}

func hidesetUnion(hs1 *Hideset, hs2 *Hideset) *Hideset {
    var head Hideset
    cur := &head
    for hs1 != nil {
        cur.next = newHideset(hs1.name)
        cur = cur.next
        hs1 = hs1.next
    }
    cur.next = hs2
    return head.next
}

func hidesetContains(hs *Hideset, s string) bool {
    for hs != nil {
        if hs.name == s {
            return true
        }
        hs = hs.next
    }
    return false
}

func hidesetIntersection(hs1 *Hideset, hs2 *Hideset) *Hideset {
    var head Hideset
    cur := &head
    for hs1 != nil {
        if hidesetContains(hs2, hs1.name) {
            cur.next = newHideset(hs1.name)
            cur = cur.next
        }
        hs1 = hs1.next
    }
    return head.next
}

func addHideset(tok *Token, hs *Hideset) *Token {
    var head Token
    cur := &head
    for tok != nil {
        t := copyToken(tok)
        t.hideset = hidesetUnion(t.hideset, hs)
        cur.next = t
        cur = cur.next
        tok = tok.next
    }
    return head.next
} 

// Appends tok2 to the end of tok1.
func appendTokens(tok1 *Token, tok2 *Token) *Token {
    if tok1.kind == TK_EOF {
        return tok2
    }
    var head Token
    cur := &head
    for tok1.kind != TK_EOF {
        cur.next = copyToken(tok1)
        cur = cur.next
        tok1 = tok1.next
    }
    cur.next = tok2
    return head.next
}

func skipCondIncl2(tok *Token) *Token {
    for tok.kind != TK_EOF {
        if isHash(tok) &&
                (Equal(tok.next, "if") || 
                    Equal(tok.next, "ifdef") ||
                    Equal(tok.next, "ifndef")) {
            tok = skipCondIncl2(tok.next.next)
            continue
        }
        if isHash(tok) && Equal(tok.next, "endif") {
            return tok.next.next
        }
        tok = tok.next
    }
    return tok
} 

// Skips until next `#else`, `#elif` or `#endif`.
// Nested `#if` and `#endif` are skipped.
func skipCondIncl(tok *Token) *Token {
    for tok.kind != TK_EOF {
        if isHash(tok) &&
                (Equal(tok.next, "if") || 
                    Equal(tok.next, "ifdef") ||
                    Equal(tok.next, "ifndef")) {
            tok = skipCondIncl2(tok.next.next)
            continue
        }
        if isHash(tok) &&
                (Equal(tok.next, "elif") || 
                    Equal(tok.next, "else") ||
                    Equal(tok.next, "endif")) {
            break
        }
        tok = tok.next
    }
    return tok
}

// Double-quotes a given string and returns it.
func quoteString(str string) []byte {
    n := len(str)
    bufsize := 3
    for i := 0; i < n; i++ {
        if str[i] == '\\' || str[i] == '"' {
            bufsize++
        }
        bufsize++
    }
    buf := make([]byte, bufsize)
    buf[0] = '"'
    p := 1
    for i := 0; i < n; i++ {
        if str[i] == '\\' || str[i] == '"' {
            buf[p] = '\\'
            p++
        }
        buf[p] = str[i]
        p++
    }
    buf[p] = '"'
    buf[p+1] = 0
    return buf
}

func newStrToken(str string, tmpl *Token) *Token {
    buf := quoteString(str)
    return Tokenize(NewFile(tmpl.file.name, tmpl.file.fileNo, buf))
}

// Copies all tokens until the next newline, terminates them with
// an EOF token and then returns them. This function is used to
// create a new list of tokens for `#if` arguments.
func copyLine(tok *Token) (rest *Token, out *Token) {
    var head Token
    cur := &head
    for !tok.atBol {
        cur.next = copyToken(tok)
        cur = cur.next
        tok = tok.next
    }
    cur.next = newEof(tok)
    rest = tok
    out = head.next
    return
}

func newNumToken(val int, tmpl *Token) *Token {
    buf := []byte(fmt.Sprintf("%d\n", val))
    buf = append(buf, 0)
    return Tokenize(NewFile(tmpl.file.name, tmpl.file.fileNo, buf))
} 

func readConstExpr(tok *Token) (rest *Token, out *Token) {
    rest, tok = copyLine(tok)

    var head Token
    cur := &head

    for tok.kind != TK_EOF {
        // "defined(foo)" or "defined foo" becomes "1" if macro "foo"
        // is defined. Otherwise "0".
        if Equal(tok, "defined") {
            start := tok
            var hasParen bool
            tok, hasParen = Consume(tok.next, "(")

            if tok.kind != TK_IDENT {
                ErrorTok(start, "macro name must be an identifier")
            }
            m := findMacro(tok)
            tok = tok.next

            if hasParen {
                tok = Skip(tok, ")")
            }

            val := 0
            if m != nil {
                val = 1
            }
            cur.next = newNumToken(val, start)
            cur = cur.next
            continue
        }

        cur.next = tok
        cur = cur.next
        tok = tok.next
    }

    cur.next = tok
    out = head.next
    return
}

// Reads and evaluates a constant expression.
func evalConstExpr(tok *Token) (rest *Token, val int64) {
    start := tok
    rest, expr := readConstExpr(tok.next)
    expr = preprocess2(expr)

    if expr.kind == TK_EOF {
        ErrorTok(start, "no expression")
    }

    // [https://www.sigbus.info/n1570#6.10.1p4] The standard requires
    // we replace remaining non-macro identifiers with "0" before
    // evaluating a constant expression. For example, `#if foo` is
    // equivalent to `#if 0` if foo is not defined.
    for t := expr; t.kind != TK_EOF; t = t.next {
        if t.kind == TK_IDENT {
            next := t.next
            *t = *newNumToken(0, t)
            t.next = next
        }
    }

    // Convert pp-numbers to regular numbers
    convertPpTokens(expr)

    rest2, val := ConstExpr(expr)
    if rest2.kind != TK_EOF {
        ErrorTok(rest2, "extra token")
    }

    return
}

func pushCondIncl(tok *Token, included bool) *CondIncl {
    ci := new(CondIncl)
    ci.next = condIncl
    ci.ctx = IN_THEN
    ci.tok = tok
    ci.included = included
    condIncl = ci
    return ci
} 

func findMacro(tok *Token) *Macro {
    if tok.kind != TK_IDENT {
        return nil
    }
    m, ok := macros[string(tok.text)]
    if !ok {
        return nil
    }
    return m
} 

func addMacro(name string, isObjlike bool, body *Token) *Macro {
    m := new(Macro)
    m.name = name
    m.isObjlike = isObjlike
    m.body = body
    macros[name] = m
    return m
} 

func readMacroParams(tok *Token) (rest *Token, params *MacroParam, vaArgsName string) {
    var head MacroParam
    cur := &head

    for !Equal(tok, ")") {
        if cur != &head {
            tok = Skip(tok, ",")
        }

        if Equal(tok, "...") {
            vaArgsName = "__VA_ARGS__"
            rest = Skip(tok.next, ")")
            params = head.next
            return
        }

        if tok.kind != TK_IDENT {
            ErrorTok(tok, "expected an identifier")
        }

        if Equal(tok.next, "...") {
            vaArgsName = string(tok.text)
            rest = Skip(tok.next.next, ")")
            params = head.next
            return
        }

        m := new(MacroParam)
        m.name = string(tok.text)
        cur.next = m
        cur = cur.next
        tok = tok.next
    }

    rest = tok.next
    params = head.next
    return
}

func readMacroDefinition(tok *Token) *Token {
    var rest *Token

    if tok.kind != TK_IDENT {
        ErrorTok(tok, "macro name must be an identifier")
    }
    name := string(tok.text)
    tok = tok.next

    if !tok.hasSpace && Equal(tok, "(") {
        // Function-like macro
        var params *MacroParam
        var vaArgsName string
        tok, params, vaArgsName = readMacroParams(tok.next)
        rest, tok = copyLine(tok)
        m := addMacro(name, false, tok)
        m.params = params
        m.vaArgsName = vaArgsName
    } else {
        // Object-like macro
        rest, tok = copyLine(tok)
        addMacro(name, true, tok)
    }

    return rest
} 

func readMacroArgOne(tok *Token, readRest bool) (rest *Token, arg *MacroArg) {
    var head Token
    cur := &head
    level := 0

    for {
        if level == 0 && Equal(tok, ")") {
            break
        }
        if level == 0 && !readRest && Equal(tok, ",") {
            break
        }

        if tok.kind == TK_EOF {
            ErrorTok(tok, "premature end of input")
        }

        switch {
        case Equal(tok, "("):
            level++
        case Equal(tok, ")"):
            level--
        }

        cur.next = copyToken(tok)
        cur = cur.next
        tok = tok.next
    }

    cur.next = newEof(tok)

    arg = new(MacroArg)
    arg.tok = head.next
    rest = tok
    return
}

func readMacroArgs(tok *Token, params *MacroParam, vaArgsName string) (
        rest *Token, args *MacroArg) {
    start := tok
    tok = tok.next.next

    var head MacroArg
    cur := &head

    pp := params
    for pp != nil {
        if cur != &head {
            tok = Skip(tok, ",")
        }
        tok, cur.next = readMacroArgOne(tok, false)
        cur = cur.next
        cur.name = pp.name
        pp = pp.next
    }

    if len(vaArgsName) != 0 {
        var arg *MacroArg
        if Equal(tok, ")") {
            arg = new(MacroArg)
            arg.tok = newEof(tok)
        } else {
            if pp != params {
                tok = Skip(tok, ",")
            }
            tok, arg = readMacroArgOne(tok, true)
        }
        arg.name = vaArgsName
        arg.isVaArgs = true
        cur.next = arg
        cur = cur.next
    } else {
        if pp != nil {
            ErrorTok(start, "too many arguments")
        }
    }

    Skip(tok, ")")
    rest = tok
    args = head.next
    return
}

func findArg(args *MacroArg, tok *Token) *MacroArg {
    text := string(tok.text)
    for ap := args; ap != nil; ap = ap.next {
        if ap.name == text {
            return ap
        }
    }
    return nil
}
 
// Concatenates all tokens in `tok` and returns a new string.
func joinTokens(tok *Token, end *Token) string {
    // Compute the length of the resulting token.
    n := 0
    for t := tok; t != end && t.kind != TK_EOF; t = t.next {
        if t != tok && t.hasSpace {
            n++
        }
        n += len(t.text)
    }

    buf := make([]byte, n)

    // Copy token texts.
    pos := 0
    for t := tok; t != end && t.kind != TK_EOF; t = t.next {
        if t != tok && t.hasSpace {
            buf[pos] = ' '
            pos++
        }
        copy(buf[pos:], t.text)
        pos += len(t.text)
    }

    return string(buf)
}
 
// Concatenates all tokens in `arg` and returns a new string token.
// This function is used for the stringizing operator (#).
func stringize(hash *Token, arg *Token) *Token {
    // Create a new string token. We need to set some value to its
    // source location for error reporting function, so we use a macro
    // name token as a template.
    s := joinTokens(arg, nil)
    return newStrToken(s, hash)
}

// Concatenates two tokens to create a new token.
func paste(lhs *Token, rhs *Token) *Token {
    // Paste the two tokens.
    n1 := len(lhs.text)
    n2 := len(rhs.text)
    buf := make([]byte, n1+n2+1)
    copy(buf, lhs.text)
    copy(buf[n1:], rhs.text)
    buf[n1+n2] = 0

    // Tokenize the resulting string.
    tok := Tokenize(NewFile(lhs.file.name, lhs.file.fileNo, buf))
    if tok.next.kind != TK_EOF {
        ErrorTok(lhs, "pasting forms '%s', an invalid token", string(buf))
    }
    return tok
} 

func hasVarargs(args *MacroArg) bool {
    for ap := args; ap != nil; ap = ap.next {
        if ap.name == "__VA_ARGS__" {
            return (ap.tok.kind != TK_EOF)
        }
    }
    return false
} 

// Replaces func-like macro parameters with given arguments.
func subst(tok *Token, args *MacroArg) *Token {
    var head Token
    cur := &head

    for tok.kind != TK_EOF {
        // "#" followed by a parameter is replaced with stringized actuals.
        if Equal(tok, "#") {
            arg := findArg(args, tok.next)
            if arg == nil {
                ErrorTok(tok.next, "'#' is not followed by a macro parameter")
            }
            cur.next = stringize(tok, arg.tok)
            cur = cur.next
            tok = tok.next.next
            continue
        }

        // [GNU] If __VA_ARG__ is empty, `,##__VA_ARGS__` is expanded
        // to the empty token list. Otherwise, its expaned to `,` and
        // __VA_ARGS__.
        if Equal(tok, ",") && Equal(tok.next, "##") {
            arg := findArg(args, tok.next.next)
            if arg != nil && arg.isVaArgs {
                if arg.tok.kind == TK_EOF {
                    tok = tok.next.next.next
                } else {
                    cur.next = copyToken(tok)
                    cur = cur.next
                    tok = tok.next.next
                }
                continue
            }
        }

        if Equal(tok, "##") {
            if cur == &head {
                ErrorTok(tok, "'##' cannot appear at start of macro expansion")
            }

            if tok.next.kind == TK_EOF {
                ErrorTok(tok, "'##' cannot appear at end of macro expansion")
            }

            arg := findArg(args, tok.next)
            if arg != nil {
                if arg.tok.kind != TK_EOF {
                    *cur = *paste(cur, arg.tok)
                    for t := arg.tok.next; t.kind != TK_EOF; t = t.next {
                        cur.next = copyToken(t)
                        cur = cur.next
                    }
                }
                tok = tok.next.next
                continue
            }

            *cur = *paste(cur, tok.next)
            tok = tok.next.next
            continue
        }

        arg := findArg(args, tok)

        if arg != nil && Equal(tok.next, "##") {
            rhs := tok.next.next

            if arg.tok.kind == TK_EOF {
                arg2 := findArg(args, rhs)
                if arg2 != nil {
                    for t := arg2.tok; t.kind != TK_EOF; t = t.next {
                        cur.next = copyToken(t)
                        cur = cur.next
                    }
                } else {
                    cur.next = copyToken(rhs)
                    cur = cur.next
                }
                tok = rhs.next
                continue
            }

            for t := arg.tok; t.kind != TK_EOF; t = t.next {
                cur.next = copyToken(t)
                cur = cur.next
            }
            tok = tok.next
            continue
        }

        // If __VA_ARG__ is empty, __VA_OPT__(x) is expanded to the
        // empty token list. Otherwise, __VA_OPT__(x) is expanded to x.
        if Equal(tok, "__VA_OPT__") && Equal(tok.next, "(") {
            var arg2 *MacroArg
            tok, arg2 = readMacroArgOne(tok.next.next, true)
            if hasVarargs(args) {
                for t := arg2.tok; t.kind != TK_EOF; t = t.next {
                    cur.next = t
                    cur = cur.next
                }
            }
            tok = Skip(tok, ")")
            continue
        }

        // Handle a macro token. Macro arguments are completely macro-expanded
        // before they are substituted into a macro body.
        if arg != nil {
            t := preprocess2(arg.tok)
            t.atBol = tok.atBol
            t.hasSpace = tok.hasSpace
            for t.kind != TK_EOF {
                cur.next = copyToken(t)
                cur = cur.next
                t = t.next
            }
            tok = tok.next
            continue
        }

        // Handle a non-macro token.
        cur.next = copyToken(tok)
        cur = cur.next
        tok = tok.next
        continue
    }

    cur.next = tok
    return head.next
}

// If tok is a macro, expands it and returns true.
// Otherwise, does nothing and returns false.
func expandMacro(tok *Token) (rest *Token, expanded bool) {
    rest = tok
    expanded = false

    if hidesetContains(tok.hideset, string(tok.text)) {
        return
    }

    m := findMacro(tok)
    if m == nil {
        return
    }

    // Built-in dynamic macro application such as __LINE__
    if m.handler != nil {
        rest = m.handler(tok)
        rest.next = tok.next
        expanded = true
        return
    }

    // Object-like macro application
    if m.isObjlike {
        hs := hidesetUnion(tok.hideset, newHideset(m.name))
        body := addHideset(m.body, hs)
        for t := body; t.kind != TK_EOF; t = t.next {
            t.origin = tok
        }
        rest = appendTokens(body, tok.next)
        rest.atBol = tok.atBol
        rest.hasSpace = tok.hasSpace
        expanded = true
        return
    }

    // If a funclike macro token is not followed by an argument list,
    // treat it as a normal identifier.
    if !Equal(tok.next, "(") {
        return
    }

    // Function-like macro application
    macroToken := tok
    tok, args := readMacroArgs(tok, m.params, m.vaArgsName)
    rparen := tok

    // Tokens that consist a func-like macro invocation may have different
    // hidesets, and if that's the case, it's not clear what the hideset
    // for the new tokens should be. We take the interesection of the
    // macro token and the closing parenthesis and use it as a new hideset
    // as explained in the Dave Prossor's algorithm.
    hs := hidesetIntersection(macroToken.hideset, rparen.hideset)
    hs = hidesetUnion(hs, newHideset(m.name))

    body := subst(m.body, args)
    body = addHideset(body, hs)
    for t := body; t.kind != TK_EOF; t = t.next {
        t.origin = macroToken
    }
    rest = appendTokens(body, tok.next)
    rest.atBol = macroToken.atBol
    rest.hasSpace = macroToken.hasSpace
    expanded = true
    return
}

func SearchIncludePaths(filename string) (path string, found bool) {
    if filename[0] == '/' {
        path = filename
        found = true
        return
    }

    cached, ok := includeCache[filename]
    if ok {
        path = cached
        found = true
        return
    }

    // Search a file from the include paths.
    for i, temp := range includePaths {
        temp += "/" + filename
        if FileExists(temp) {
            includeCache[filename] = temp
            includeNextIdx = i + 1
            path = temp
            found = true
            return
        }
    }

    found = false
    return
}

func searchIncludeNext(filename string) (path string, found bool) {
    for includeNextIdx < len(includePaths) {
        temp := includePaths[includeNextIdx] + "/" + filename
        if FileExists(temp) {
            path = temp
            found = true
            return
        }
        includeNextIdx++
    }
    found = false
    return
}
 
// Reads an #include argument.
func readIncludeFilename(tok *Token) (rest *Token, filename string, isDquote bool) {
    // Pattern 1: #include "foo.h"
    if tok.kind == TK_STR {
        // A double-quoted filename for #include is a special kind of
        // token, and we don't want to interpret any escape sequences in it.
        // For example, "\f" in "C:\foo" is not a formfeed character but
        // just two non-control characters, backslash and f.
        // So we don't want to use token->str.
        isDquote = true
        rest = skipLine(tok.next)
        n := len(tok.text)
        filename = string(tok.text[1:n-1])
        return
    }

    // Pattern 2: #include <foo.h>
    if Equal(tok, "<") {
        // Reconstruct a filename from a sequence of tokens between
        // "<" and ">".
        start := tok

        // Find closing ">".
        for !Equal(tok, ">") {
            if tok.atBol || tok.kind == TK_EOF {
                ErrorTok(tok, "expected '>'")
            }
            tok = tok.next
        }

        isDquote = false
        rest = skipLine(tok.next)
        filename = joinTokens(start.next, tok)
        return
    }

    // Pattern 3: #include FOO
    // In this case FOO must be macro-expanded to either
    // a single string token or a sequence of "<" ... ">".
    if tok.kind == TK_IDENT {
        var tok2 *Token
        rest, tok2 = copyLine(tok)
        tok2 = preprocess2(tok2)
        _, filename, isDquote = readIncludeFilename(tok2)
        return
    }

    ErrorTok(tok, "expected a filename")
    return
}

// Detects the following "include guard" pattern.
//
//   #ifndef FOO_H
//   #define FOO_H
//   ...
//   #endif
func detectIncludeGuard(tok *Token) (guard string, ok bool) {
    ok = false

    // Detect the first two lines.
    if !isHash(tok) || !Equal(tok.next, "ifndef") {
        return
    }
    tok = tok.next.next

    if tok.kind != TK_IDENT {
        return
    }

    macro := string(tok.text)
    tok = tok.next

    if !isHash(tok) || !Equal(tok.next, "define") || !Equal(tok.next.next, macro) {
        return
    }

    // Read until the end of the file.
    for tok.kind != TK_EOF {
        if !isHash(tok) {
            tok = tok.next
            continue
        }

        if Equal(tok.next, "endif") && tok.next.next.kind == TK_EOF {
            guard = macro
            ok = true
            return
        }

        if Equal(tok, "if") || Equal(tok, "ifdef") || Equal(tok, "ifndef") {
            tok = skipCondIncl(tok.next)
        } else {
            tok = tok.next
        }
    }
  
    return
}

func includeFile(tok *Token, path string, filenameTok *Token) *Token {
    // Check for "#pragma once"
    if pragmaOnce[path] {
        return tok
    }

    // If we read the same file before, and if the file was guarded
    // by the usual #ifndef ... #endif pattern, we may be able to
    // skip the file without opening it.
    guardName, ok := includeGuards[path]
    if ok {
        _, ok = macros[guardName]
        if ok {
            return tok
        }
    }

    tok2, err := TokenizeFile(path)
    if err != nil {
        ErrorTok(filenameTok, "%s: cannot open file: %s", path, err.Error())
    }

    guardName, ok = detectIncludeGuard(tok2)
    if ok {
        includeGuards[path] = guardName
    }

    return appendTokens(tok2, tok)
}

// Reads #line arguments
func readLineMarker(tok *Token) *Token {
    start := tok
    rest, tok := copyLine(tok)
    tok = Preprocess(tok)

    if tok.kind != TK_NUM || tok.ty.kind != TY_INT {
        ErrorTok(tok, "invalid line marker")
    }
    start.file.lineDelta = int(tok.val) - start.lineNo

    tok = tok.next
    if tok.kind == TK_EOF {
        return rest
    }

    if tok.kind != TK_STR {
        ErrorTok(tok, "filename expected")
    }
    start.file.displayName = GetStr(tok)
    return rest
}

// Visits all tokens in `tok` while evaluating preprocessing
// macros and directives.
func preprocess2(tok *Token) *Token { 
    var head Token
    cur := &head

    for tok.kind != TK_EOF {
        // If it is a macro, expand it.
        var ok bool
        tok, ok = expandMacro(tok)
        if ok {
            continue
        }

        // Pass through if it is not a "#".
        if !isHash(tok) {
            tok.lineDelta = tok.file.lineDelta
            tok.filename = tok.file.displayName
            cur.next = tok
            cur = cur.next
            tok = tok.next
            continue
        }

        start := tok
        tok = tok.next

        if Equal(tok, "include") {
            var filename string
            var isDquote bool
            tok, filename, isDquote = readIncludeFilename(tok.next)

            if filename[0] != '/' && isDquote {
                path := DirName(start.file.name) + "/" + filename
                if FileExists(path) {
                    tok = includeFile(tok, path, start.next.next)
                    continue
                }
            }

            path, ok := SearchIncludePaths(filename)
            if !ok {
                path = filename
            }
            tok = includeFile(tok, path, start.next.next)
            continue
        }

        if Equal(tok, "include_next") {
            var filename string
            tok, filename, _ = readIncludeFilename(tok.next)
            path, ok := searchIncludeNext(filename)
            if !ok {
                path = filename
            }
            tok = includeFile(tok, path, start.next.next)
            continue
        }

        if Equal(tok, "define") {
            tok = readMacroDefinition(tok.next)
            continue
        }

        if Equal(tok, "undef") {
            tok = tok.next
            if tok.kind != TK_IDENT {
                ErrorTok(tok, "macro name must be an identifier")
            }
            UndefMacro(string(tok.text))
            tok = skipLine(tok.next)
            continue
        }

        if Equal(tok, "if") {
            var val int64
            tok, val = evalConstExpr(tok)
            pushCondIncl(start, (val!=0))
            if val == 0 {
                tok = skipCondIncl(tok)
            }
            continue
        }

        if Equal(tok, "ifdef") {
            defined := findMacro(tok.next)
            pushCondIncl(tok, (defined!=nil))
            tok = skipLine(tok.next.next)
            if defined == nil {
                tok = skipCondIncl(tok)
            }
            continue
        }

        if Equal(tok, "ifndef") {
            defined := findMacro(tok.next)
            pushCondIncl(tok, (defined==nil))
            tok = skipLine(tok.next.next)
            if defined != nil {
                tok = skipCondIncl(tok)
            }
            continue
        }

        if Equal(tok, "elif") {
            if condIncl == nil || condIncl.ctx == IN_ELSE {
                ErrorTok(start, "stray #elif")
            }
            condIncl.ctx = IN_ELIF
            if !condIncl.included {
                var val int64
                tok, val = evalConstExpr(tok)
                if val != 0 {
                    condIncl.included = true
                    continue
                }
            }
            tok = skipCondIncl(tok)
            continue
        }

        if Equal(tok, "else") {
            if condIncl == nil || condIncl.ctx == IN_ELSE {
                ErrorTok(start, "stray #else")
            }
            condIncl.ctx = IN_ELSE
            tok = skipLine(tok.next)
            if condIncl.included {
                tok = skipCondIncl(tok)
            }
            continue
        }

        if Equal(tok, "endif") {
            if condIncl == nil {
                ErrorTok(start, "stray #endif")
            }
            condIncl = condIncl.next
            tok = skipLine(tok.next)
            continue
        }

        if Equal(tok, "line") {
            tok = readLineMarker(tok.next)
            continue
        }

        if tok.kind == TK_PP_NUM {
            tok = readLineMarker(tok)
            continue
        }

        if Equal(tok, "pragma") && Equal(tok.next, "once") {
            pragmaOnce[tok.file.name] = true
            tok = skipLine(tok.next.next)
            continue
        }

        if Equal(tok, "pragma") {
            for {
                tok = tok.next
                if tok.atBol {
                    break
                }
            }
            continue
        }

        if Equal(tok, "error") {
            ErrorTok(tok, "error")
        }

        // `#`-only line is legal. It's called a null directive.
        if tok.atBol {
            continue
        }

        ErrorTok(tok, "invalid preprocessor directive")
    }

    cur.next = tok
    return head.next
}

func DefineMacro(name string, buf string) {
    temp := []byte(buf)
    temp = append(temp, 0)
    tok := Tokenize(NewFile("<built-in>", 1, temp))
    addMacro(name, true, tok)
}

func UndefMacro(name string) {
    delete(macros, name)
}

func addBuiltin(name string, fn MacroHandlerFn) *Macro {
    m := addMacro(name, true, nil)
    m.handler = fn
    return m
}

func fileMacro(tmpl *Token) *Token {
    for tmpl.origin != nil {
        tmpl = tmpl.origin
    }
    return newStrToken(tmpl.file.displayName, tmpl)
} 

func lineMacro(tmpl *Token) *Token {
    for tmpl.origin != nil {
        tmpl = tmpl.origin
    }
    i := tmpl.lineNo + tmpl.file.lineDelta
    return newNumToken(i, tmpl)
}

// __COUNTER__ is expanded to serial values starting from 0.
func counterMacro(tmpl *Token) *Token {
    i := counterNextIdx
    counterNextIdx++
    return newNumToken(i, tmpl)
}

// __TIMESTAMP__ is expanded to a string describing the last
// modification time of the current file. E.g.
// "Fri Jul 24 01:32:50 2020"
func timestampMacro(tmpl *Token) *Token {
    buf := time.Now().Format("Mon Jan 02 15:04:05 2006")
    return newStrToken(buf, tmpl)
}

func baseFileMacro(tmpl *Token) *Token {
    return newStrToken(baseFile, tmpl)
}

// __DATE__ is expanded to the current date, e.g. "May 17 2020".
func formatDate(tm time.Time) string {
    return fmt.Sprintf("\"%s %2d %d\"", tm.Month().String(), tm.Day(), tm.Year())
}

// __TIME__ is expanded to the current time, e.g. "13:34:03".
func formatTime(tm time.Time) string {
  return fmt.Sprintf("\"%02d:%02d:%02d\"", tm.Hour(), tm.Minute(), tm.Second())
} 

func InitMacros() {
    // Define predefined macros
    DefineMacro("_LP64", "1")
    DefineMacro("__C99_MACRO_WITH_VA_ARGS", "1")
    DefineMacro("__ELF__", "1")
    DefineMacro("__LP64__", "1")
    DefineMacro("__SIZEOF_DOUBLE__", "8")
    DefineMacro("__SIZEOF_FLOAT__", "4")
    DefineMacro("__SIZEOF_INT__", "4")
    DefineMacro("__SIZEOF_LONG_DOUBLE__", "8")
    DefineMacro("__SIZEOF_LONG_LONG__", "8")
    DefineMacro("__SIZEOF_LONG__", "8")
    DefineMacro("__SIZEOF_POINTER__", "8")
    DefineMacro("__SIZEOF_PTRDIFF_T__", "8")
    DefineMacro("__SIZEOF_SHORT__", "2")
    DefineMacro("__SIZEOF_SIZE_T__", "8")
    DefineMacro("__SIZE_TYPE__", "unsigned long")
    DefineMacro("__STDC_HOSTED__", "1")
    DefineMacro("__STDC_NO_COMPLEX__", "1")
    DefineMacro("__STDC_UTF_16__", "1")
    DefineMacro("__STDC_UTF_32__", "1")
    DefineMacro("__STDC_VERSION__", "201112L")
    DefineMacro("__STDC__", "1")
    DefineMacro("__USER_LABEL_PREFIX__", "")
    DefineMacro("__alignof__", "_Alignof")
    DefineMacro("__amd64", "1")
    DefineMacro("__amd64__", "1")
    DefineMacro("__chibicc__", "1")
    DefineMacro("__const__", "const")
    DefineMacro("__gnu_linux__", "1")
    DefineMacro("__inline__", "inline")
    DefineMacro("__linux", "1")
    DefineMacro("__linux__", "1")
    DefineMacro("__signed__", "signed")
    DefineMacro("__typeof__", "typeof")
    DefineMacro("__unix", "1")
    DefineMacro("__unix__", "1")
    DefineMacro("__volatile__", "volatile")
    DefineMacro("__x86_64", "1")
    DefineMacro("__x86_64__", "1")
    DefineMacro("linux", "1")
    DefineMacro("unix", "1")

    addBuiltin("__FILE__", fileMacro)
    addBuiltin("__LINE__", lineMacro)
    addBuiltin("__COUNTER__", counterMacro)
    addBuiltin("__TIMESTAMP__", timestampMacro)
    addBuiltin("__BASE_FILE__", baseFileMacro)

    tm := time.Now()
    DefineMacro("__DATE__", formatDate(tm))
    DefineMacro("__TIME__", formatTime(tm))
}

type StringKind int

const (
    STR_NONE StringKind = iota
    STR_UTF8
    STR_UTF16
    STR_UTF32
    STR_WIDE
)

func getStringKind(tok *Token) StringKind {
    if string(tok.text) == "u8" {
        return STR_UTF8
    }
    switch tok.text[0] {
    case '"': 
        return STR_NONE
    case 'u': 
        return STR_UTF16
    case 'U': 
        return STR_UTF32
    case 'L': 
        return STR_WIDE
    }
    Unreachable()
    return STR_NONE
} 

// Concatenates adjacent string literals into a single string literal
// as per the C spec.
func joinAdjacentStringLiterals(tok *Token) {
    // First pass: If regular string literals are adjacent to wide
    // string literals, regular string literals are converted to a wide
    // type before concatenation. In this pass, we do the conversion.
    for tok1 := tok; tok1.kind != TK_EOF; {
        if tok1.kind != TK_STR || tok1.next.kind != TK_STR {
            tok1 = tok1.next
            continue
        }

        kind := getStringKind(tok1)
        basety := tok1.ty.base

        for t := tok1.next; t.kind == TK_STR; t = t.next {
            k := getStringKind(t)
            if kind == STR_NONE {
                kind = k
                basety = t.ty.base
            } else {
                if k != STR_NONE && kind != k {
                    ErrorTok(t, "unsupported non-standard concatenation of string literals")
                }
            }
        }

        if basety.size > 1 {
            for t := tok1; t.kind == TK_STR; t = t.next {
                if t.ty.base.size == 1 {
                    *t = *tokenizeStringLiteral(t, basety)
                }
            }
        }

        for tok1.kind == TK_STR {
            tok1 = tok1.next
        }
    }

    // Second pass: concatenate adjacent string literals.
    for tok1 := tok; tok1.kind != TK_EOF; {
        if tok1.kind != TK_STR || tok1.next.kind != TK_STR {
            tok1 = tok1.next
            continue
        }

        tok2 := tok1.next
        for tok2.kind == TK_STR {
            tok2 = tok2.next
        }

        n := tok1.ty.arrayLen
        for t := tok1.next; t != tok2; t = t.next {
            n += t.ty.arrayLen - 1
        }

        var (
            str []byte
            utf16 []uint16
            utf32[] uint32
        )

        // trailing zero is set implicitly by slice initialization
        switch tok1.ty.base.size {
        case 1:
            str = make([]byte, n)
            i := 0
            for t := tok1; t != tok2; t = t.next {
                copy(str[i:], t.str)
                i += t.ty.arrayLen - 1
            }
        case 2:
            utf16 = make([]uint16, n)
            i := 0
            for t := tok1; t != tok2; t = t.next {
                copy(utf16[i:], t.utf16)
                i += t.ty.arrayLen - 1
            }
        case 4:
            utf32 = make([]uint32, n)
            i := 0
            for t := tok1; t != tok2; t = t.next {
                copy(utf32[i:], t.utf32)
                i += t.ty.arrayLen - 1
            }
        default:
            Unreachable()
        }

        *tok1 = *copyToken(tok1)
        tok1.ty = ArrayOf(tok1.ty.base, n)
        tok1.str = str
        tok1.utf16 = utf16
        tok1.utf32 = utf32
        tok1.next = tok2
        tok1 = tok2
    }
}

//
//    Public functions
//

func Preprocess(tok *Token) *Token {
    tok = preprocess2(tok)
    if condIncl != nil {
        ErrorTok(condIncl.tok, "unterminated conditional directive")
    }
    convertPpTokens(tok)
    joinAdjacentStringLiterals(tok)

    for t := tok; t != nil; t = t.next {
        t.lineNo += t.lineDelta
    }
    return tok
}

