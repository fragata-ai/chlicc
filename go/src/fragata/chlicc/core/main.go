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
    "bytes"
    "fmt"
//    "io/ioutil"
    "os"
)

//
//    Options
//

type Options struct {
    OptInclude []string
    OptE bool
    OptM bool
    OptMD bool
    OptO string
    OutputFile string
    IncludePaths []string
    BaseFile string
}

//
//    Public state variables
//

var (
    includePaths []string
    baseFile string
)

//
//    Private functions
//

func mustTokenizeFile(path string) (tok *Token, err error) {
    tok, err = TokenizeFile(path)
    if tok == nil {
        err = fmt.Errorf("%s: %s", path, err.Error())
        return
    }
    return
} 

func concatTokens(tok1 *Token, tok2 *Token) *Token {
    // This is slightly different from 'appendTokens' in 'preprocess.go'
    if tok1 == nil || tok1.kind == TK_EOF {
        return tok2
    }

    t := tok1
    for t.next.kind != TK_EOF {
        t = t.next
    }
    t.next = tok2
    return tok1
} 

func openFile(path string) (out *os.File, err error) {
    if len(path) != 0 || path == "-" {
        out = os.Stdout
        return
    }

    out, err = os.Open(path)
    if err != nil {
        err = fmt.Errorf("cannot open output file: %s: %s", path, err.Error())
        return
    }

    return
} 

// Prints tokens to stdout. Used for -E.
func printTokens(tok *Token, opt *Options) error {
    fname := opt.OptO
    if len(fname) == 0 {
        fname = "-"
    }
    out, err := openFile(fname)
    if err != nil {
        return err
    }

    line := 1
    for ; tok.kind != TK_EOF; tok = tok.next {
        if line > 1 && tok.atBol {
            fmt.Fprintf(out, "\n")
        }
        if tok.hasSpace && !tok.atBol {
            fmt.Fprintf(out, " ")
        }
        fmt.Fprintf(out, "%s", string(tok.text))
        line++
    }
    fmt.Fprintf(out, "\n")

    return nil
} 

// If -M options is given, the compiler writes a list of input files to
// stdout in a format that "make" command can read. This feature is
// used to automate file dependency management.
func printDependencies() error { 
    // SKIPPED
    return nil
}

//
//    Public functions
//

func FileExists(path string) bool {
    stat, err := os.Stat(path)
    if err != nil {
        return false
    }
    return (stat.Mode() & os.ModeType == 0)
}

func Compile(opt *Options) error {
    var err error
    var tok *Token

    includePaths = opt.IncludePaths
    baseFile = opt.BaseFile

    // Process -include option
    for _, incl := range(opt.OptInclude) {
        var path string
        if FileExists(incl) {
            path = incl
        } else {
            var ok bool
            path, ok = SearchIncludePaths(incl)
            if !ok {
                return fmt.Errorf("-include: %s: file not found", incl)
            }
        }

        var tok2 *Token
        tok2, err = mustTokenizeFile(path)
        if err != nil {
            return err
        }
        tok = concatTokens(tok, tok2)
    }

    // Tokenize and parse.
    tok2, err := mustTokenizeFile(opt.BaseFile)
    if err != nil {
        return err
    }
    tok = concatTokens(tok, tok2)
    tok = Preprocess(tok)

    // If -M or -MD are given, print file dependencies.
    if opt.OptM || opt.OptMD {
        err = printDependencies()
        if err != nil {
            return err
        }
        if opt.OptM {
            return nil
        }
    }

    // If -E is given, print out preprocessed C code as a result.
    if opt.OptE {
        err = printTokens(tok, opt)
        if err != nil {
            return err
        }
        return nil
    }

    prog := Parse(tok)

    // Open a temporary output buffer.
    var buf bytes.Buffer

    // Traverse the AST to emit assembly.
    Codegen(prog, &buf)

/*
    // Write the asembly text to a file.
    err = ioutil.WriteFile(opt.OutputFile, buf.Bytes(), 0666)
    if err != nil {
        return err
    }
*/

    return nil
}

