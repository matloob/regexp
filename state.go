// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package regexp

// TODO(matloob): rename all the upper-case identifiers to lower-case.

import (
	"bytes"
	"strconv"
)


// just use ints instead of stateinst??
type stateInst int

type State struct {
	// Instruction pointers in the state.
	// TODO(matloob): Should these have a different type?
	inst []int

	// Empty string bitfield flags in effect on the way
	// into this state, along with FlagMatch if this is
	// a matching state.
	flag flag

	// Outgoing arrows from State, one per input byte class.
	next []*State
}

func (s *State) isMatch() bool {
	return s.flag & flagMatch != 0
}

func dumpState(state *State) string {
	return state.Dump()
}


type flag uint32

var (
	flagEmptyMask = flag(0xFFF)
	flagMatch   = flag(0x1000)
	flagLastWord  = flag(0x2000)
	flagNeedShift = flag(16)
)

// Special "firstbyte" values for a state.  (Values >= 0 denote actual bytes.)
const (
	fbUnknown = -1 // No analysis has been performed.
	fbMany    = -2 // Many bytes will lead out of this state.
	fbNone    = -3 // No bytes lead out of this state.
)

const (
	// Indices into start for unanchored searches.
	// Add startAnchored for anchored searches.
	startBeginText        = 0
	startBeginLine        = 2
	startWordBoundary    = 4
	startNonWordBoundary = 6
	maxStart              = 8

	kStartAnchored = 1
)

var mark stateInst = -1

// TODO(matloob): in RE2 deadState and fullMatchState are (State*)(1) and (State*)(2)
// respectively. Is it cheaper to compare with those numbers, than these states?
// Do we need to import package unsafe?
var deadState = &State{}
var fullMatchState = &State{}

func isSpecialState(s *State) bool {
	// see above. cc does int comparison because deadState and fullMatchState
	// are special numbers, but that's unsafe.
	// TODO(matloob): convert states back to numbers. (pointers into state array state(-2) and state(-1))
	return s == deadState || s == fullMatchState || s == nil
}

func (s *State) Dump() string {
	switch s {
	case nil:
		return "_"
	case deadState:
		return "X"
	case fullMatchState:
		return "*"
	}
	var buf bytes.Buffer
	sep := ""
	buf.WriteString("(0x<TODO(matloob):state id>)")
	// buf.WriteString(fmt.Sprintf("(%p)", s)
	for _, inst := range s.inst {
		if inst == int(mark) {
			buf.WriteString("|")
			sep = ""
		} else {
			buf.WriteString(sep)
			buf.WriteString(strconv.Itoa(inst))
			sep = ","
		}
	}
	buf.WriteString("flag=0x")
	buf.WriteString(strconv.FormatUint(uint64(s.flag), 16))
	return buf.String()
}

type stateSet struct {
	states []*State
}

// inst, flag, next

func (s *stateSet) find(state *State) *State {
loop:
	for i := range s.states {
		if len(s.states[i].inst) != len(state.inst) {
			continue
		}
		for j := range state.inst {
			if s.states[i].inst[j] != state.inst[j] {
				continue loop
			}
		}
		if s.states[i].flag != state.flag {
			continue
		}
		return s.states[i]
	}
	return nil
}

func (s *stateSet) size() int {
	return len(s.states)
}

func (s *stateSet) insert(state *State) {
	s.states = append(s.states, state)
}

type startInfo struct {
	start *State
	firstbyte int64
}
