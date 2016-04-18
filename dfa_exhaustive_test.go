package regexp

import (
	"bufio"
	"compress/bzip2"
	"io"
	"os"
	"strconv"
	"strings"
	"testing"
	
	"fmt"
)

func TestDFAZVV(t *testing.T) {
	testDFA(t, "testdata/re2-search.txt")
}


// THIS IS REALLY SLOW
func TestDFAExhaustive(t *testing.T) {
	testDFA(t, "testdata/re2-exhaustive.txt.bz2")
}

func testDFA(t *testing.T, file string) {
	f, err := os.Open(file)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	var txt io.Reader
	if strings.HasSuffix(file, ".bz2") {
		z := bzip2.NewReader(f)
		txt = z
		file = file[:len(file)-len(".bz2")] // for error messages
	} else {
		txt = f
	}
	lineno := 0
	scanner := bufio.NewScanner(txt)
	var (
		str       []string
		input     []string
		inStrings bool
		q, full   string
		nfail     int
		ncase     int
	)
	for lineno := 1; scanner.Scan(); lineno++ {
		fmt.Println(lineno, "  ",  ncase)
		line := scanner.Text()
		switch {
		case line == "":
			t.Fatalf("%s:%d: unexpected blank line", file, lineno)
		case line[0] == '#':
			continue
		case 'A' <= line[0] && line[0] <= 'Z':
			// Test name.
			t.Logf("%s\n", line)
			continue
		case line == "strings":
			str = str[:0]
			inStrings = true
		case line == "regexps":
			inStrings = false
		case line[0] == '"':
			q, err = strconv.Unquote(line)
			if err != nil {
				// Fatal because we'll get out of sync.
				t.Fatalf("%s:%d: unquote %s: %v", file, lineno, line, err)
			}
			if inStrings {
				str = append(str, q)
				continue
			}
			// Is a regexp.
			if len(input) != 0 {
				t.Fatalf("%s:%d: out of sync: have %d strings left before %#q", file, lineno, len(input), q)
			}
			full = `\A(?:` + q + `)\z`
			input = str
		case line[0] == '-' || '0' <= line[0] && line[0] <= '9':
			// A sequence of match results.
			ncase++
			if len(input) == 0 {
				t.Fatalf("%s:%d: out of sync: no input remaining", file, lineno)
			}
			var text string
			text, input = input[0], input[1:]
			if strings.Contains(q, `\C`) || (!isSingleBytes(text) && strings.Contains(q, `\B`)) {
				// RE2's \B considers every byte position,
				// so it sees 'not word boundary' in the
				// middle of UTF-8 sequences. This package
				// only considers the positions between runes,
				// so it disagrees. Skip those cases.
				continue
			}
			res := strings.Split(line, ";")
			if len(res) != len(run) {
				t.Fatalf("%s:%d: have %d test results, want %d", file, lineno, len(res), len(run))
			}
			for i := range res {
				have, suffix := dfarun[i](q, full, text)
				want := parseResult(t, file, lineno, res[i])
				if len(want) <= 2 && !same(have, want) {
					t.Errorf("%s:%d: %#q%s.FindSubmatchIndex(%#q) = %v, want %v", file, lineno, q, suffix, text, have, want)
					if nfail++; nfail >= 100 {
						t.Fatalf("stopping after %d errors", nfail)
					}
					continue
				}
				b, suffix := dfamatch[i](q, full, text)
				if b != (want != nil) {
					t.Errorf("%s:%d: %#q%s.MatchString(%#q) = %v, want %v", file, lineno, q, suffix, text, b, !b)
					if nfail++; nfail >= 100 {
						t.Fatalf("stopping after %d errors", nfail)
					}
					continue
				}
			}

		default:
			t.Fatalf("%s:%d: out of sync: %s\n", file, lineno, line)
		}
	}
	if err := scanner.Err(); err != nil {
		t.Fatalf("%s:%d: %v", file, lineno, err)
	}
	if len(input) != 0 {
		t.Fatalf("%s:%d: out of sync: have %d strings left at EOF", file, lineno, len(input))
	}
	t.Logf("%d cases tested", ncase)
}

// TODO(matloob): This is deceptive because we're not reusing the DFA between
// tests. FIX IT!

var dfarun = []func(string, string, string) ([]int, string){
	dfarunFull,
	dfarunPartial,
	dfarunFullLongest,
	dfarunPartialLongest,
}

func dfarunFull(re, refull, text string) ([]int, string) {
	return dfaSubmatchIndex(refull, text, false), "[full]"
}

func dfarunPartial(re, refull, text string) ([]int, string) {
	return dfaSubmatchIndex(re, text, false), ""
}

func dfarunFullLongest(re, refull, text string) ([]int, string) {
	return dfaSubmatchIndex(refull, text, true), "[full,longest]"
}

func dfarunPartialLongest(re, refull, text string) ([]int, string) {
	return dfaSubmatchIndex(re, text, true), "[longest]"
}

func dfaSubmatchIndex(re, text string, longest bool) []int {
	i, j, b, err := matchDFA2(re, text, longest)
	if err != nil || !b {
		return nil
	}
	return []int{i, j}
}

var dfamatch = []func(string, string, string) (bool, string){
	dfamatchFull,
	dfamatchPartial,
	dfamatchFullLongest,
	dfamatchPartialLongest,
}

func dfamatchFull(re, refull, text string) (bool, string) {
	return dfaMatchString(refull, text, false), "[full]"
}

func dfamatchPartial(re, refull, text string) (bool, string) {
	return dfaMatchString(re, text, false), ""
}

func dfamatchFullLongest(re, refull, text string) (bool, string) {
	return dfaMatchString(refull, text, true), "[full,longest]"
}

func dfamatchPartialLongest(re, refull, text string) (bool, string) {
	return dfaMatchString(re, text, true), "[longest]"
}

func dfaMatchString(re, text string, longest bool) bool {
	_, _, b, err := matchDFA2(re, text, longest)
	return err == nil && b
}
