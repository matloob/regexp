package dfa

import (
	"errors"
	"matloob.io/regexp/syntax"
	"matloob.io/regexp/internal/input"
)

type Searcher struct {
	expr string
	prog *syntax.Prog
	fdfa, ldfa, revdfa *DFA
}

func (s *Searcher) Init(prog *syntax.Prog, expr string) {
	s.prog = prog
	s.expr = expr
}

var errNotDFA = errors.New("can't use dfa")

func (s *Searcher) Search(i input.Input, pos int, longest bool, matchcap *[]int, ncap int) (bool, error) {
	if reverse(i) == nil {
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
			s.revdfa = newReverseDFA(revprog, longestMatch, 50000)
		}
		var matched bool
		*matchcap = (*matchcap)[:ncap]
		p, ep, matched, err := dfa.search(i, pos, s.revdfa)
		if err != nil {
			return false, errNotDFA
		}
		if ncap > 0 {
			(*matchcap)[0], (*matchcap)[1] = p, ep
		}
		return matched, nil
} 