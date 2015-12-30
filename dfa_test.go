package regexp

import (
	"matloob.io/regexp/syntax"
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

	i := &inputString{input}
	j, k, b := d.search(i)
	return j, k, b, nil
}

func TestDFA(t *testing.T) {

	// These are all anchored matches.
	testCases := []struct {
		re   string
		in   string
		want bool
	}{
		// anchored
		{"abc", "abc", true},
		{"abc", "ab", false},
		{".*(a|z)bc", "eedbcxcee", false},
		{"^abc", "xxxabcxxx", false},
		// unanchored
		{"abc", "xxxabcxxx", true},
	}
	for _, tc := range testCases {
		_, _, got, err := matchDFA(tc.re, tc.in)
		if err != nil {
			t.Error(err)
		}
		if got != tc.want {
			t.Errorf("matchDFA(%q, %q): got %v, want %v", tc.re, tc.in, got, tc.want)
		}
	}

	{
		i, j, m, err := matchDFA("abc", "xxxabcxxx")
		if err != nil {
			t.Error(err)
		}
		t.Log(i, j)
		if i != 3 || j != 6 {
			t.Errorf("matchDFA(...) is wrong... got %v, %v, %v want %v, %v, %v", i, j, m, 3, 6, true)
		}
	}

}
