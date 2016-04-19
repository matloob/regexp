// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package dfa

import (
	"fmt"
	"sort"
	"unicode"
	"matloob.io/regexp/internal/input"
	"matloob.io/regexp/syntax"
)

type rangeMap struct {
	bytemap []int
	divides []rune
}

// Looks up bytes in d.bytemap but handles case c == kByteEndText too.
func (rm *rangeMap) lookup(r rune) int {
	fmt.Println(r)
	// Use the trivial byte map for now...
	// See ComputeByteMap
	if r == input.EndOfText {
		fmt.Println("end of text", len(rm.divides))
		return len(rm.divides)
	}
	if r == input.StartOfText {
		return len(rm.divides) + 1
	}
	if r > 255 {
		// binary search for the range
		lo, hi := 0, len(rm.divides)
		for {
			// search rm.divides
			center := (lo + hi) / 2
			if center == lo {
				return lo
			}
			divcenter := rm.divides[center]
			if r >= divcenter {
				lo = center
			} else {
				hi = center
			}
		}
	}
	return rm.bytemap[int(r)]
}

// count returns the number of ranges. 0 <= rm.count() < rm.lookup(r) for all runes r.
func (rm *rangeMap) count() int {
	return len(rm.divides) + 2
}

func (rm *rangeMap) init(prog *syntax.Prog) {
	divides := make(map[rune]bool)
	for _, inst := range prog.Inst {
		switch inst.Op {
		case syntax.InstRune:
			if len(inst.Rune) == 1 {
				r0 := inst.Rune[0]
				divides[r0] = true
				divides[r0+1] = true
				if syntax.Flags(inst.Arg)&syntax.FoldCase != 0 {
					for r1 := unicode.SimpleFold(r0); r1 != r0; r1 = unicode.SimpleFold(r1) {

						divides[r1] = true

						divides[r1+1] = true
					}
				}
				break
			} else {
				for i := 0; i < len(inst.Rune); i += 2 {
					divides[inst.Rune[i]] = true
					divides[inst.Rune[i+1]+1] = true
					if syntax.Flags(inst.Arg)&syntax.FoldCase != 0 {
						rl := inst.Rune[i]
						rh := inst.Rune[i+1]
						for r0 := rl; r0 <= rh; r0++ {
							// range mapping doesn't commute...
							for r1 := unicode.SimpleFold(r0); r1 != r0; r1 = unicode.SimpleFold(r1) {
								divides[r1] = true

								divides[r1+1] = true
							}
						}
					}
				}
			}

		case syntax.InstRune1:
			r0 := inst.Rune[0]
			divides[r0] = true
			divides[r0+1] = true
			if syntax.Flags(inst.Arg)&syntax.FoldCase != 0 {
				for r1 := unicode.SimpleFold(r0); r1 != r0; r1 = unicode.SimpleFold(r1) {
					divides[r1] = true
					divides[r1+1] = true
				}
			}
		case syntax.InstRuneAnyNotNL:
			divides['\n'] = true
			divides['\n'+1] = true

		case syntax.InstEmptyWidth:
			switch syntax.EmptyOp(inst.Arg) {
			case syntax.EmptyBeginLine, syntax.EmptyEndLine:
				divides['\n'] = true
				divides['\n'+1] = true
			case syntax.EmptyWordBoundary, syntax.EmptyNoWordBoundary:
				// can we turn this into an InstRune?
				divides['A'] = true
				divides['Z'+1] = true
				divides['a'] = true
				divides['z'+1] = true
				divides['0'] = true
				divides['9'+1] = true
				divides['_'] = true
				divides['_'+1] = true
			}
		}
	}

	divl := make([]rune, 0, len(divides))
	divl = append(divl, -1)
	for r := range divides {
		divl = append(divl, r)
	}
	runeSlice(divl).Sort()
	rm.divides = divl
	rm.bytemap = make([]int, 256)
	k := 0
	for i := range rm.bytemap {
		if divides[rune(i)] {
			k++
		}
		rm.bytemap[i] = k
	}
}

// runeSlice exists to permit sorting the case-folded rune sets.
type runeSlice []rune

func (p runeSlice) Len() int           { return len(p) }
func (p runeSlice) Less(i, j int) bool { return p[i] < p[j] }
func (p runeSlice) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }

// Sort is a convenience method.
func (p runeSlice) Sort() {
	sort.Sort(p)
}
