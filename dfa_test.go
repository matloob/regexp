package regexp

import (
	"matloob.io/regexp/syntax"
	"fmt"
	"testing"
)



func matchDFA(regexp string, input string) (int, int, bool, error) {
	re, err := syntax.Parse(regexp, syntax.Flags(0))
	if err != nil {
		return 0, 0, false, err
	}
	prog, err := syntax.Compile(re)
	if err != nil {
		return 0, 0, false, err
	}

	d := newDFA(prog, longestMatch, 0)
	d.BuildAllStates()

	revprog, err := syntax.CompileReversed(re)
	if err != nil {
		panic("failed to compile reverse prog")
	}

	reversed := newDFA(revprog, longestMatch, 0)
	if reversed.BuildAllStates() == 0 {
		fmt.Println("Failed to build all states")
	}

	i := &inputString{input}
	j, k, b := d.search(i,0,reversed)
	return j, k, b, nil
}

func TestDFA(t *testing.T) {
	// These are all anchored matches.
	testCases := []struct {
		re   string
		in   string
		wantS int
		wantE int
		want bool
	}{

		{"abc", "abc", 0, 3, true},
		{"abc", "ab", -1, -1, false},
		{".*(a|z)bc", "eedbcxcee", -1, -1,false},
		{"^abc", "xxxabcxxx", -1, -1, false},

		{"ab*", "xxxabbxxx", 3, 6, true},
		{"abc", "xxxabcxxx", 3, 6, true},

		{"(>[^\n]+)?\n", ">One Homo sapiens alu\nGGCCGGGCGCG", 0, 22, true},
		{"abc","abcxxxabc", 0,3,true},
	}
	for _, tc := range testCases {
		i, j, got, err := matchDFA(tc.re, tc.in)
		if err != nil {
			t.Error(err)
		}
		if got != tc.want || i != tc.wantS  || j != tc.wantE {
			t.Errorf("matchDFA(%q, %q): got (%v, %v, %v), want (%v, %v, %v)", tc.re, tc.in, i, j, got, tc.wantS, tc.wantE, tc.want)
		}
	}

}