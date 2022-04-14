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

import "unicode/utf8"

//
//    Private static data
//

var rangeIdent1 = [...]rune{
    '_', '_', 
    'a', 'z', 
    'A', 'Z', 
    '$', '$',
    0x00A8, 0x00A8, 
    0x00AA, 0x00AA, 
    0x00AD, 0x00AD, 
    0x00AF, 0x00AF,
    0x00B2, 0x00B5, 
    0x00B7, 0x00BA, 
    0x00BC, 0x00BE, 
    0x00C0, 0x00D6,
    0x00D8, 0x00F6, 
    0x00F8, 0x00FF, 
    0x0100, 0x02FF, 
    0x0370, 0x167F,
    0x1681, 0x180D, 
    0x180F, 0x1DBF, 
    0x1E00, 0x1FFF, 
    0x200B, 0x200D,
    0x202A, 0x202E, 
    0x203F, 0x2040, 
    0x2054, 0x2054, 
    0x2060, 0x206F,
    0x2070, 0x20CF, 
    0x2100, 0x218F, 
    0x2460, 0x24FF, 
    0x2776, 0x2793,
    0x2C00, 0x2DFF, 
    0x2E80, 0x2FFF, 
    0x3004, 0x3007, 
    0x3021, 0x302F,
    0x3031, 0x303F, 
    0x3040, 0xD7FF, 
    0xF900, 0xFD3D, 
    0xFD40, 0xFDCF,
    0xFDF0, 0xFE1F, 
    0xFE30, 0xFE44, 
    0xFE47, 0xFFFD,
    0x10000, 0x1FFFD, 
    0x20000, 0x2FFFD, 
    0x30000, 0x3FFFD, 
    0x40000, 0x4FFFD,
    0x50000, 0x5FFFD, 
    0x60000, 0x6FFFD, 
    0x70000, 0x7FFFD, 
    0x80000, 0x8FFFD,
    0x90000, 0x9FFFD, 
    0xA0000, 0xAFFFD, 
    0xB0000, 0xBFFFD, 
    0xC0000, 0xCFFFD,
    0xD0000, 0xDFFFD, 
    0xE0000, 0xEFFFD, 
    -1,
}

var rangeIdent2 = [...]rune{
    '0', '9', 
    '$', '$', 
    0x0300, 0x036F, 
    0x1DC0, 0x1DFF, 
    0x20D0, 0x20FF,
    0xFE20, 0xFE2F, 
    -1,
}

//
//    Private functions
//

func inRange(rng []rune, c rune) bool {
    for i := 0; rng[i] != -1; i += 2 {
        if rng[i] <= c && c <= rng[i+1] {
            return true
        }
    }
    return false
}

//
//    Public functions
//

func EncodeUtf8(buf []byte, p int, c int) int {
    n := utf8.EncodeRune(buf[p:], rune(c))
    return p + n
}

func DecodeUtf8(buf []byte, p int) (c int, newPos int) {
    r, n := utf8.DecodeRune(buf[p:])
    c = int(r)
    newPos = p + n
    return
}

// [https://www.sigbus.info/n1570#D] C11 allows not only ASCII but
// some multibyte characters in certan Unicode ranges to be used in an
// identifier.
//
// This function returns true if a given character is acceptable as
// the first character of an identifier.
func IsIdent1(c int) bool {
    return inRange(rangeIdent1[:], rune(c))
}

// Returns true if a given character is acceptable as a non-first
// character of an identifier.
func IsIdent2(c int) bool {
    return (IsIdent1(c) || inRange(rangeIdent2[:], rune(c)))
}

func DisplayWidth(buf []byte) int {
    return utf8.RuneCount(buf)
}

