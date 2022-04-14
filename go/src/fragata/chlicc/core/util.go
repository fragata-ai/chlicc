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
    "encoding/binary"
    "path/filepath"
    "strings"
)

//
//    Public functions
//

func IntMax(x int, y int) int {
    if x > y {
        return x
    } else {
        return y
    }
}

func IntMin(x int, y int) int {
    if x < y {
        return x
    } else {
        return y
    }
}

func StrChr(buf []byte, p int, c byte) int {
    n := bytes.IndexByte(buf[p:], c)
    if n < 0 {
        return -1
    }
    return p + n
}

func StrStr(buf []byte, p int, s string) int {
    n := bytes.Index(buf[p:], []byte(s))
    if n < 0 {
        return -1
    }
    return p + n
}

func IsSpace(c byte) bool {
    return (c == ' ' || c == '\f' || c == '\n' || c == '\r' || c == '\t' || c == '\v')
}

func IsPunct(c byte) bool {
    return (c > 0x20 && c < 0x7f && !IsAlnum(c))
}

func IsAlnum(c byte) bool {
    return ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9'))
}

func IsDigit(c byte) bool {
    return (c >= '0' && c <= '9')
}

func IsXDigit(c byte) bool {
    return ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f'))
}

func StartsWith(p []byte, q string) bool {
    lenp := len(p)
    lenq := len(q)
    return (lenp >= lenq && string(p[:lenq]) == q)
} 

func StartsWithNoCase(p []byte, q string) bool {
    lenp := len(p)
    lenq := len(q)
    return (lenp >= lenq && strings.ToLower(string(p[:lenq])) == strings.ToLower(q))
} 

func EndsWith(p []byte, q string) bool {
    lenp := len(p)
    lenq := len(q)
    return (lenp >= lenq && string(p[lenp-lenq:]) == q)
} 

func EndsWithNoCase(p []byte, q string) bool {
    lenp := len(p)
    lenq := len(q)
    return (lenp >= lenq && strings.ToLower(string(p[lenp-lenq:])) == strings.ToLower(q))
} 

func EncodeFloat(buf []byte, val float32) {
    var b bytes.Buffer
    binary.Write(&b, binary.LittleEndian, &val)
    copy(buf[:4], b.Bytes())
}

func EncodeDouble(buf []byte, val float64) {
    var b bytes.Buffer
    binary.Write(&b, binary.LittleEndian, &val)
    copy(buf[:8], b.Bytes())
}

func DirName(path string) string {
    return filepath.Dir(path)
}

func Unreachable() {
    panic("Unreachable")
}

