// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package dfa

import (
	"errors"
	"math"
	"matloob.io/regexp/internal/input"
	"matloob.io/regexp/syntax"
)

type Searcher struct {
	expr               string
	prog               *syntax.Prog
	fdfa, ldfa, revdfa *DFA
}

func (s *Searcher) Init(prog *syntax.Prog, expr string) {
	s.prog = prog
	s.expr = expr
}

var errNotDFA = errors.New("can't use dfa")

func (s *Searcher) Search(i input.Input, pos int, longest bool, matchcap *[]int, ncap int) (bool, error) {
	rinput, ok := i.(input.Rinput)
	if !ok {
		return false, errNotDFA
	}
	var dfa *DFA
	if longest {
		if s.ldfa == nil {
			s.ldfa = newDFA(s.prog, longestMatch, 10000)
		}
		dfa = s.ldfa
	} else {
		if s.fdfa == nil {
			s.fdfa = newDFA(s.prog, firstMatch, 10000)
		}
		dfa = s.fdfa
	}
	if s.revdfa == nil {
		// XXX find me a good home
		// recreate syntax.Regexp (we shouldn't need to do thi)
		re, err := syntax.Parse(s.expr, syntax.Perl)
		if err != nil {
			panic("parse failed")
		}
		re.Simplify()
		revprog, err := syntax.CompileReversed(re)
		if err != nil {
			panic("CompileReversed failed")
		}
		s.revdfa = newDFA(revprog, longestMatch, 50000)
	}
	var matched bool
	*matchcap = (*matchcap)[:ncap]
	p, ep, matched, err := search(dfa, s.revdfa, rinput, pos)
	if err != nil {
		return false, errNotDFA
	}
	if ncap > 0 {
		(*matchcap)[0], (*matchcap)[1] = p, ep
	}
	return matched, nil
}

type searchParams struct {
	input            input.Rinput
	startpos          int
	anchored          bool
	wantEarliestMatch bool
	runForward        bool
	start             *State
	firstbyte         int64 // int64 to be compatible with atomic ops
	failed            bool  // "out" parameter: whether search gave up
	ep                int   // "out" parameter: end pointer for match

	matches []int
}

func search(d, reversed *DFA, i input.Rinput, startpos int) (start int, end int, matched bool, err error) {
	params := searchParams{}
	params.startpos = startpos
	params.wantEarliestMatch = false
	params.input = i
	params.runForward = true
	params.ep = int(math.MaxInt64)
	if !d.analyzeSearch(&params) {
		return -1, -1, false, errors.New("analyze search failed on forward DFA")
	}
	b := d.searchLoop(&params)
	if params.failed {
		return -1, -1, false, errFallBack
	}
	if !b {
		return -1, -1, false, nil
	}
	end = params.ep

	params = searchParams{}
	params.startpos = startpos
	params.ep = end
	params.anchored = true
	params.input = i
	params.runForward = false
	if !reversed.analyzeSearch(&params) {
		return -2, -2, false, errors.New("analyze search failed on reverse DFA")
	}
	b = reversed.searchLoop(&params)
	if DebugDFA {
		DebugPrintf("\nkind %d\n%v\n", d.kind, d.prog)
	}
	if params.failed {
		return -1, -1, false, errFallBack
	}
	return params.ep, end, b, nil
}