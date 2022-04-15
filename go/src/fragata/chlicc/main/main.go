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

package main

import (
    "fmt"
    "os"
    "fragata/chlicc/core"
)

func main() {
    args := os.Args
    if len(args) != 3 {
        fmt.Fprintf(os.Stderr, "Usage: chlicc <input> <output>\n")
        os.Exit(1)
    }
    input := args[1]
    output := args[2]
    err := Main(input, output)
    if err != nil {
        fmt.Fprintf(os.Stderr, "Error: %s\n", err.Error())
        os.Exit(1)
    }
}

func Main(input string, output string) error {
    core.InitMacros()
    opt := &core.Options{
        IncludePaths: []string{"test", "include"},
        BaseFile: input,
        OutputFile: output,
        OptFcommon: true, // default
    }
    err := core.Compile(opt)
    if err != nil {
        return err
    }
    fmt.Printf("Done\n")
    return nil
}

