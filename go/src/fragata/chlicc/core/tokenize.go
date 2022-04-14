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
    "io/ioutil"
    "os"
    "strconv"
)

//
//    TokenKind
//

type TokenKind int

const (
    TK_IDENT TokenKind = iota // Identifiers
    TK_PUNCT                  // Punctuators
    TK_KEYWORD                // Keywords
    TK_STR                    // String literals
    TK_NUM                    // Numeric literals
    TK_PP_NUM                 // Preprocessing numbers
    TK_EOF                    // End-of-file markers
)

//
//    File
//

type File struct {
    name string
    fileNo int
    contents []byte

    // For #line directive
    displayName string
    lineDelta int
}

//
//    Token
//

type Token struct {
    kind TokenKind   // Token kind
    next *Token      // Next token
    val int64        // If kind is TK_NUM, its value
    fval float64     // If kind is TK_NUM, its value
    loc int          // Token location
    text []byte      // Token contents
    ty *Type         // Used if TK_NUM or TK_STR
    str []byte       // String literal contents including terminating '\0'
    utf16 []uint16   // UTF-16 string literal --"--
    utf32 []uint32   // UTF-16 string literal --"--
    file *File       // Source location
    filename string  // Filename
    lineNo int       // Line number
    lineDelta int    // Line number
    atBol bool       // True if this token is at beginning of line
    hasSpace bool    // True if this token follows a space character
    hideset *Hideset // For macro expansion
    origin *Token    // If this is expanded from a macro, the original token
} 

//
//    Private state variables
//

var (
    // Input file
    currentFile *File

    // A list of all input files.
    inputFiles []*File

    // True if the current position is at the beginning of a line
    atBol bool

    // True if the current position follows a space character
    hasSpace bool
)

//
//    Public functions
//

// Reports an error and exit.
func Error(format string, args ...interface{}) {
    fmt.Fprintf(os.Stderr, format, args...)
    fmt.Fprintf(os.Stderr, "\n")
    os.Exit(1)
}

// Reports an error message in the following format.
//
// foo.c:10: x = y + 1;
//               ^ <error message here>
func VerrorAt(
        filename string, 
        buf []byte,
        lineNo int,
        loc int, 
        format string, 
        args ...interface{}) {
    // Find a line containing `loc`.
    line := loc
    for line > 0 && buf[line-1] != '\n' {
        line--
    }

    end := loc
    for end < len(buf) && buf[end] != '\n' {
        end++
    }

    // Print out the line.
    indent, _ := fmt.Fprintf(os.Stderr, "%s:%d: ", filename, lineNo)
    fmt.Fprintf(os.Stderr, "%s\n", buf[line:end])

    // Show the error message.
    pos := DisplayWidth(buf[line:loc]) + indent

    fmt.Fprintf(os.Stderr, "%*s", pos, "") // print pos spaces.
    fmt.Fprintf(os.Stderr, "^ ")
    fmt.Fprintf(os.Stderr, format, args...)
    fmt.Fprintf(os.Stderr, "\n")
}

func ErrorAt(loc int, format string, args ...interface{}) {
    lineNo := 1
    for p := 0; p < loc; p++ {
        if currentFile.contents[p] == '\n' {
            lineNo++
        }
    }
    VerrorAt(currentFile.name, currentFile.contents, lineNo, loc, format, args...)
    os.Exit(1)
}

func ErrorTok(tok *Token, format string, args ...interface{}) {
    VerrorAt(tok.file.name, tok.file.contents, tok.lineNo, tok.loc, format, args...)
    os.Exit(1)
}

func WarnTok(tok *Token, format string, args ...interface{}) {
    VerrorAt(tok.file.name, tok.file.contents, tok.lineNo, tok.loc, format, args...)
}

func GetStr(tok *Token) string {
    // remove terminating '\0' if any
    n := len(tok.str)
    if n > 0 && tok.str[n-1] == 0 {
        n--
    }
    return string(tok.str[:n])
}

// Consumes the current token if it matches `op`.
func Equal(tok *Token, op string) bool {
    return (string(tok.text) == op)
} 

func EqualAny(tok *Token, ops ...string) bool {
    text := string(tok.text)
    for _, op := range ops {
        if text == op {
            return true
        }
    }
    return false
} 

// Ensure that the current token is `op`.
func Skip(tok *Token, op string) *Token {
    if !Equal(tok, op) {
        ErrorTok(tok, "expected '%s'", op)
    }
    return tok.next
} 

func Consume(tok *Token, op string) (*Token, bool) {
    if Equal(tok, op) {
        return tok.next, true
    }
    return tok, false
} 

func ConsumeAny(tok *Token, ops ...string) (*Token, bool) {
    if EqualAny(tok, ops...) {
        return tok.next, true
    }
    return tok, false
} 

//
//    Private functions
//

// Creates a new token.
func newToken(kind TokenKind, buf []byte, start int, end int) *Token {
    tok := new(Token)
    tok.kind = kind
    tok.loc = start
    tok.text = buf[start:end]
    tok.file = currentFile
    tok.filename = currentFile.displayName
    tok.atBol = atBol
    tok.hasSpace = hasSpace
    atBol = false
    hasSpace = false
    return tok
} 

// Reads an identifier and returns the length of it.
// If p does not point to a valid identifier, 0 is returned.
func readIdent(buf []byte, start int) int {
    p := start
    v, p := DecodeUtf8(buf, p)
    if !IsIdent1(v) {
        return 0
    }

    for {
        v, q := DecodeUtf8(buf, p)
        if !IsIdent2(v) {
            return p - start
        }
        p = q
    }
} 

func fromHex(c byte) int {
    if '0' <= c && c <= '9' {
        return int(c) - '0'
    }
    if 'a' <= c && c <= 'f' {
        return int(c) - 'a' + 10
    }
    return int(c) - 'A' + 10
} 

var punctTable = [...]string{
    "<<=", 
    ">>=", 
    "...", 
    "==", 
    "!=", 
    "<=", 
    ">=", 
    "->", 
    "+=",
    "-=", 
    "*=", 
    "/=", 
    "++", 
    "--", 
    "%=", 
    "&=", 
    "|=", 
    "^=", 
    "&&",
    "||", 
    "<<", 
    ">>", 
    "##",
}

// Reads a punctuator token from p and returns its length.
func readPunct(buf []byte, p int) int {
    for _, kw := range punctTable {
        if StartsWith(buf[p:], kw) {
            return len(kw)
        }
    }
    if IsPunct(buf[p]) {
        return 1
    }
    return 0
}

var kwTable = map[string]bool{
    "return": true, 
    "if": true, 
    "else": true, 
    "for": true, 
    "while": true, 
    "int": true, 
    "sizeof": true, 
    "char": true,
    "struct": true, 
    "union": true, 
    "short": true, 
    "long": true, 
    "void": true, 
    "typedef": true, 
    "_Bool": true,
    "enum": true, 
    "static": true, 
    "goto": true, 
    "break": true, 
    "continue": true, 
    "switch": true, 
    "case": true,
    "default": true, 
    "extern": true, 
    "_Alignof": true, 
    "_Alignas": true, 
    "do": true, 
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
    "asm": true, 
    "_Thread_local": true, 
    "__thread": true, 
    "_Atomic": true,
    "__attribute__": true, 
}

func isKeyword(tok *Token) bool {
    return kwTable[string(tok.text)]
}

func readEscapedChar(buf []byte, p int) (v int, newPos int) {
    c := buf[p]
    if '0' <= c && c <= '7' {
        // Read an octal number.
        v = int(c) - '0'
        p++
        c = buf[p]
        if '0' <= c && c <= '7' {
            v = (v << 3) + (int(c) - '0')
            p++
            c = buf[p]
            if '0' <= c && c <= '7' {
                v = (v << 3) + (int(c) - '0')
                p++
            }
        }
        newPos = p
        return
    }

    if c == 'x' {
        // Read a hexadecimal number.
        p++
        c = buf[p]
        if !IsXDigit(c) {
            ErrorAt(p, "invalid hex escape sequence")
        }
        v = fromHex(c)
        p++
        for {
            c = buf[p]
            if !IsXDigit(c) {
                break
            }
            v = (v << 4) + fromHex(c)
            p++
        }
        newPos = p
        return
    }

    newPos = p + 1

    // TODO: Check whether the following statement makes sense
    //     for the compiler written in Go.

    // Escape sequences are defined using themselves here. E.g.
    // '\n' is implemented using '\n'. This tautological definition
    // works because the compiler that compiles our compiler knows
    // what '\n' actually is. In other words, we "inherit" the ASCII
    // code of '\n' from the compiler that compiles our compiler,
    // so we don't have to teach the actual code here.
    //
    // This fact has huge implications not only for the correctness
    // of the compiler but also for the security of the generated code.
    // For more info, read "Reflections on Trusting Trust" by Ken Thompson.
    // https://github.com/rui314/chibicc/wiki/thompson1984.pdf

    switch c {
    case 'a':
        v = '\a'
    case 'b':
        v = '\b'
    case 't':
        v = '\t'
    case 'n': 
        v = '\n'
    case 'v': 
        v = '\v'
    case 'f': 
        v = '\f'
    case 'r':
        v = '\r'
    // [GNU] \e for the ASCII escape character is a GNU C extension.
    case 'e': 
        v = 27
    default:
        v = int(c)
    }

    return
}

// Finds a closing double-quote.
func stringLiteralEnd(buf []byte, p int) int {
    start := p
    for {
        c := buf[p]
        if c == '"' {
            break
        }
        if c == '\n' || c == 0 {
            ErrorAt(start, "unclosed string literal")
        }
        if c == '\\' {
            p++
        }
        p++
    }
    return p
} 

func readStringLiteral(buf []byte, start int, quote int) *Token {
    end := stringLiteralEnd(buf, quote+1)
    out := make([]byte, end-quote)
    n := 0

    var v int

    for p := quote + 1; p < end; {
        c := buf[p]
        if c == '\\' {
            v, p = readEscapedChar(buf, p+1)
            out[n] = byte(v)
            n++
        } else {
            out[n] = c
            n++
            p++
        }
    }

    tok := newToken(TK_STR, buf, start, end+1)
    tok.ty = ArrayOf(TyChar, n+1)
    tok.str = out
    return tok
}
 
// Reads a UTF-8-encoded string literal and transcodes it in UTF-16.
//
// UTF-16 is yet another variable-width encoding for Unicode. Code
// points smaller than U+10000 are encoded in 2 bytes. Code points
// equal to or larger than that are encoded in 4 bytes. Each 2 bytes
// in the 4 byte sequence is called "surrogate", and a 4 byte sequence
// is called a "surrogate pair".
func readUtf16StringLiteral(buf []byte, start int, quote int) *Token {
    end := stringLiteralEnd(buf, quote+1)
/* TODO: Report apparent bug in original code
    out := make([]uint16, end-start)
*/
    out := make([]uint16, end-quote)
    n := 0

    var v int

    for p := quote + 1; p < end; {
        if (buf[p] == '\\') {
            v, p = readEscapedChar(buf, p + 1)
            out[n] = uint16(v)
            n++
            continue
        }

        v, p = DecodeUtf8(buf, p)
        if (v < 0x10000) {
            // Encode a code point in 2 bytes.
            out[n] = uint16(v)
            n++
        } else {
            // Encode a code point in 4 bytes.
            v -= 0x10000
            out[n] = uint16(0xd800+((v>>10)&0x3ff))
            out[n+1] = uint16(0xdc00+(v&0x3ff))
            n += 2
        }
    }

    tok := newToken(TK_STR, buf, start, end+1)
    tok.ty = ArrayOf(TyUshort, n+1)
    tok.utf16 = out
    return tok
}
 
// Reads a UTF-8-encoded string literal and transcodes it in UTF-32.
//
// UTF-32 is a fixed-width encoding for Unicode. Each code point is
// encoded in 4 bytes.
func readUtf32StringLiteral(buf []byte, start int, quote int, ty *Type) *Token {
    end := stringLiteralEnd(buf, quote+1)
    out := make([]uint32, end-quote)
    n := 0

    var v int

    for p := quote + 1; p < end; {
        if buf[p] == '\\' {
            v, p = readEscapedChar(buf, p+1)
        } else {
            v, p = DecodeUtf8(buf, p)
        }
        out[n] = uint32(v)
        n++
    }

    tok := newToken(TK_STR, buf, start, end+1)
    tok.ty = ArrayOf(ty, n+1)
    tok.utf32 = out
    return tok
}

func readCharLiteral(buf []byte, start int, quote int, ty *Type) *Token {
    p := quote + 1
    c := buf[p]
    if c == 0 {
        ErrorAt(start, "unclosed char literal")
    }

    var v int
    if c == '\\' {
        v, p = readEscapedChar(buf, p+1)
    } else {
        v, p = DecodeUtf8(buf, p)
    }

    end := StrChr(buf, p, '\'')
    if end < 0 {
        ErrorAt(p, "unclosed char literal")
    }

    tok := newToken(TK_NUM, buf, start, end+1)
    tok.val = int64(v)
    tok.ty = ty
    return tok
} 

func convertPpInt(tok *Token) bool {
    p := 0
    q := len(tok.text)

    // Read a binary, octal, decimal or hexadecimal number.
    base := 10
    switch {
    case StartsWithNoCase(tok.text, "0x") && IsXDigit(tok.text[2]):
        p += 2 
        base = 16
    case StartsWithNoCase(tok.text, "0b") && (tok.text[2] == '0' || tok.text[2] == '1'):
        p += 2
        base = 2
    case tok.text[0] == '0':
        base = 8
    }

    // Read U, L or LL suffixes.
    l := false
    u := false

    switch {
    case EndsWith(tok.text, "LLU") || EndsWith(tok.text, "LLu") ||
            EndsWith(tok.text, "llU") || EndsWith(tok.text, "llu") ||
            EndsWith(tok.text, "ULL") || EndsWith(tok.text, "Ull") ||
            EndsWith(tok.text, "uLL") || EndsWith(tok.text, "ull"):
        q -= 3
        l = true
        u = true
    case EndsWithNoCase(tok.text, "lu") || EndsWithNoCase(tok.text, "ul"):
        q -= 2
        l = true
        u = true
    case EndsWith(tok.text, "LL") || EndsWith(tok.text, "ll"):
        q -= 2
        l = true
    case tok.text[q-1] == 'L' || tok.text[q-1] == 'l':
        q--
        l = true
    case tok.text[q-1] == 'U' || tok.text[q-1] == 'u':
        q--
        u = true
    }

    val, err := strconv.ParseUint(string(tok.text[p:q]), base, 64)
    if err != nil {
        return false
    }

    // Infer a type.
    var ty *Type
    if base == 10 {
        switch {
        case l && u:
            ty = TyUlong
        case l:
            ty = TyLong
        case u:
            if val >> 32 != 0 {
                ty = TyUlong 
            } else {
                ty = TyUint
            }
        default:
            if val >> 31 != 0 {
                ty = TyLong
            } else {
                ty = TyInt
            }
        }
    } else {
        switch {
        case l && u:
            ty = TyUlong
        case l:
            if val >> 63 != 0 {
                ty = TyUlong
            } else {
                ty = TyLong
            }
        case u:
            if val >> 32 != 0 {
                ty = TyUlong
            } else {
                ty = TyUint
            }
        case val >> 63 != 0:
            ty = TyUlong
        case val >> 32 != 0:
            ty = TyLong
        case val >> 31 != 0:
            ty = TyUint
        default:
            ty = TyInt
        }
    }

    tok.kind = TK_NUM
    tok.val = int64(val)
    tok.ty = ty
    return true
}

// The definition of the numeric literal at the preprocessing stage
// is more relaxed than the definition of that at the later stages.
// In order to handle that, a numeric literal is tokenized as a
// "pp-number" token first and then converted to a regular number
// token after preprocessing.
//
// This function converts a pp-number token to a regular number token.
func convertPpNumber(tok *Token) {
    // Try to parse as an integer constant.
    if convertPpInt(tok) {
        return
    }

    // If it's not an integer, it must be a floating point constant.
    end := len(tok.text)
    var ty *Type
    switch {
    case tok.text[end-1] == 'f' || tok.text[end-1] == 'F':
        ty = TyFloat
        end--
    case tok.text[end-1] == 'l' || tok.text[end-1] == 'L':
        ty = TyLdouble
        end--
    default:
        ty = TyDouble
    }

    val, err := strconv.ParseFloat(string(tok.text[:end]), 64)
    if err != nil {
        ErrorTok(tok, "invalid numeric constant")
    }

    tok.kind = TK_NUM
    tok.fval = val
    tok.ty = ty
}

func convertPpTokens(tok *Token) {
    for t := tok; t.kind != TK_EOF; t = t.next {
        switch {
        case isKeyword(t):
            t.kind = TK_KEYWORD
        case t.kind == TK_PP_NUM:
            convertPpNumber(t)
        }
    }
}

// Initializes line info for all tokens.
func addLineNumbers(tok *Token) {
    p := 0
    n := 1
    for {
        if p == tok.loc {
            tok.lineNo = n
            tok = tok.next
        }
        c := currentFile.contents[p]
        if c == 0 {
            break
        }
        if c == '\n' {
            n++
        }
        p++
    }
}

func tokenizeStringLiteral(tok *Token, basety *Type) *Token {
    // Zeros are passed as 'start' and 'quote' as indices in
    // 'text' buffer (rather the regular token stream).
    // Correct original 'loc' is set explicitly afterwards.
    var t *Token
    if basety.size == 2 {
        t = readUtf16StringLiteral(tok.text, 0, 0)
    } else {
        t = readUtf32StringLiteral(tok.text, 0, 0, basety)
    }
    t.loc = tok.loc
    t.next = tok.next
    return t
}

// Tokenizes a given string and returns new tokens.
func Tokenize(file *File) *Token {
    currentFile = file

    var head Token
    cur := &head

    atBol = true
    hasSpace = false

    buf := file.contents
    p := 0

    for buf[p] != 0 {
        // Skip line comments.
        if StartsWith(buf[p:], "//") {
            p += 2
            for buf[p] != '\n' {
                p++
            }
            hasSpace = true
            continue
        }

        // Skip block comments.
        if StartsWith(buf[p:], "/*") {
            q := StrStr(buf, p+2, "*/")
            if q < 0 {
                ErrorAt(p, "unclosed block comment")
            }
            p = q + 2
            hasSpace = true
            continue
        }

        // Skip newline.
        if buf[p] == '\n' {
            p++
            atBol = true
            hasSpace = false
            continue
        }

        // Skip whitespace characters.
        if IsSpace(buf[p]) {
            p++
            hasSpace = true
            continue
        }

        // Numeric literal
        if IsDigit(buf[p]) || (buf[p] == '.' && IsDigit(buf[p+1])) {
            q := p
            p++
            for {
                done := true
                c := buf[p]
                switch {
                case c == 'e' || c == 'E' || c == 'p' || c == 'P':
                    done = false
                    c2 := buf[p+1]
                    if c2 == '+' || c2 == '-' {
                        p += 2
                    } else {
                        p++
                    }
                case IsAlnum(c) || c == '.':
                    done = false
                    p++
                }
                if done {
                    break
                }
            }
            cur.next = newToken(TK_PP_NUM, buf, q, p)
            cur = cur.next
            continue
        }

        // String literal
        if buf[p] == '"' {
            cur.next = readStringLiteral(buf, p, p)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // UTF-8 string literal
        if StartsWith(buf[p:], "u8\"") {
            cur.next = readStringLiteral(buf, p, p+2)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // UTF-16 string literal
        if StartsWith(buf[p:], "u\"") {
            cur.next = readUtf16StringLiteral(buf, p, p+1)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // Wide string literal
        if StartsWith(buf[p:], "L\"") {
            cur.next = readUtf32StringLiteral(buf, p, p+1, TyInt)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // UTF-32 string literal
        if StartsWith(buf[p:], "U\"") {
            cur.next = readUtf32StringLiteral(buf, p, p+1, TyUint)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // Character literal
        if buf[p] == '\'' {
            cur.next = readCharLiteral(buf, p, p, TyInt)
            cur = cur.next
            cur.val &= 0xff
            p += len(cur.text)
            continue
        }

        // UTF-16 character literal
        if StartsWith(buf[p:], "u'") {
            cur.next = readCharLiteral(buf, p, p+1, TyUshort)
            cur = cur.next
            cur.val &= 0xffff
            p += len(cur.text)
            continue
        }

        // Wide character literal
        if StartsWith(buf[p:], "L'") {
            cur.next = readCharLiteral(buf, p, p+1, TyInt)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // UTF-32 character literal
        if StartsWith(buf[p:], "U'") {
            cur.next = readCharLiteral(buf, p, p+1, TyUint)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // Identifier or keyword
        identLen := readIdent(buf, p)
        if identLen != 0 {
            cur.next = newToken(TK_IDENT, buf, p, p+identLen)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        // Punctuators
        punctLen := readPunct(buf, p)
        if punctLen != 0 {
            cur.next = newToken(TK_PUNCT, buf, p, p+punctLen)
            cur = cur.next
            p += len(cur.text)
            continue
        }

        ErrorAt(p, "invalid token")
    }

    cur.next = newToken(TK_EOF, buf, p, p)
    addLineNumbers(head.next)
    return head.next
}

// Returns the contents of a given file.
func readFile(path string) (buf []byte, err error) {
    var fp *os.File

    if path == "-" {
        // By convention, read from stdin if a given filename is "-".
        fp = os.Stdin
    } else {
        fp, err = os.Open(path)
        if err != nil {
            return
        }
        defer fp.Close()
    }

    // Read the entire file.
    buf, err = ioutil.ReadAll(fp)
    if err != nil {
        return
    }

    // Make sure that the last line is properly terminated with '\n'.
    n := len(buf)
    if n == 0 || buf[n-1] != '\n' {
        buf = append(buf, '\n')
    }

    // add null terminator for scanning convenience
    buf = append(buf, 0)

    return
} 

func GetInputFiles() []*File {
    return inputFiles
}

func NewFile(name string, fileNo int, contents []byte) *File {
    file := new(File)
    file.name = name
    file.displayName = name
    file.fileNo = fileNo
    file.contents = contents
    return file
}

// Replaces \r or \r\n with \n.
func canonicalizeNewline(buf []byte) []byte {
    i := 0
    j := 0

    for {
        c := buf[i]
        if c == 0 {
            break
        }
        if c == '\r' {
            if buf[i+1] == '\n' {
                i++
            }
            buf[j] = '\n'
            j++
            i++
        } else {
            buf[j] = c
            j++
            i++
        }
    }

    buf[j] = 0

    return buf[:j+1]
} 

// Removes backslashes followed by a newline.
func removeBackslashNewline(buf []byte) []byte {
    i := 0
    j := 0

    // We want to keep the number of newline characters so that
    // the logical line number matches the physical one.
    // This counter maintain the number of newlines we have removed.
    n := 0

    for {
        c := buf[i]
        if c == 0 {
            break
        }
        switch {
        case c == '\\' && buf[i+1] == '\n':
            i += 2
            n++
        case c == '\n':
            buf[j] = c
            j++
            i++
            for n > 0 {
                buf[j] = '\n'
                j++
                n--
            }
        default:
            buf[j] = c
            j++
            i++
        }
    }

    for n > 0 {
        buf[j] = '\n'
        j++
        n--
    }
    buf[j] = 0

    return buf[:j+1]
} 

func readUniversalChar(buf []byte) int {
    v := 0
    for _, c := range buf {
        if !IsXDigit(c) {
            return 0
        }
        v = (v << 4) | fromHex(c)
    }
    return v
}

// Replaces \u or \U escape sequences with corresponding UTF-8 bytes.
func convertUniversalChars(buf []byte) []byte {
    p := 0
    q := 0

    for buf[p] != 0 {
        switch {
        case StartsWith(buf[p:], "\\u"):
            c := readUniversalChar(buf[p+2:p+6])
            if c != 0 {
                p += 6
                q = EncodeUtf8(buf, q, c)
            } else {
                buf[q] = buf[p]
                q++
                p++
            }
        case StartsWith(buf[:p], "\\U"):
            c := readUniversalChar(buf[p+2:p+10])
            if c != 0 {
                p += 10
                q = EncodeUtf8(buf, q, c)
            } else {
                buf[q] = buf[p]
                q++
                p++
            }
        case buf[p] == '\\':
            buf[q] = buf[p]
            buf[q+1] = buf[p+1]
            q += 2
            p += 2
        default:
            buf[q] = buf[p]
            q++
            p++
        }
    }

    buf[q] = 0

    return buf[:q+1]
} 

func TokenizeFile(path string) (tok *Token, err error) {
    buf, err := readFile(path)
    if err != nil {
        return
    }

    // UTF-8 texts may start with a 3-byte "BOM" marker sequence.
    // If exists, just skip them because they are useless bytes.
    // (It is actually not recommended to add BOM markers to UTF-8
    // texts, but it's not uncommon particularly on Windows.)
    if buf[0] == 0xef && buf[1] == 0xbb && buf[2] == 0xbf {
        buf = buf[3:]
    }

    buf = canonicalizeNewline(buf)
    buf = removeBackslashNewline(buf)
    buf = convertUniversalChars(buf)

    // Save the filename for assembler .file directive.
    fileNo := len(inputFiles)
    file := NewFile(path, fileNo+1, buf)

    // Save the filename for assembler .file directive.
    inputFiles = append(inputFiles, file)

    tok = Tokenize(file)
    return
}

