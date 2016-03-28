// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package regexp

// TODO(matloob): rename all the upper-case identifiers to lower-case.

import (
	"bytes"
	"fmt"
	"math"
	"log"
	"matloob.io/regexp/syntax"
	"os"
	"sort"
	"sync"
	"sync/atomic"
)

// TODO(matloob): remove before submitting
const DebugDFA = false

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
	var str string
	sep := ""
	str += fmt.Sprintf("(%p)", s)
	for _, inst := range s.inst {
		if inst == int(mark) {
			str += "|"
			sep = ""
		} else {
			str += fmt.Sprintf("%s%d", sep, inst)
			sep = ","
		}
	}
	str += fmt.Sprintf(" flag=%#x", s.flag)
	return str
}

type sparseSet struct {
	sparseToDense []int
	dense         []int
}

func makeSparseSet(maxSize int) sparseSet {
	// 	s.maxSize = maxSize  // not necessary, right?
	return sparseSet{
		sparseToDense: make([]int, maxSize),
		dense:         make([]int, maxSize),
	}
}

func (s *sparseSet) resize(newMaxSize int) {
	// TODO(matloob): Use slice length instead of size for 'dense'.
	// Use cap instead of maxSize for both.
	size := len(s.dense)
	if size > newMaxSize {
		size = newMaxSize
	}
	if newMaxSize > len(s.sparseToDense) {
		a := make([]int, newMaxSize)
		if s.sparseToDense != nil {
			copy(a, s.sparseToDense)
		}
		s.sparseToDense = a

		a = make([]int, size, newMaxSize)
		if s.dense != nil {
			copy(a, s.dense)
		}
		s.dense = a
	}
}

func (s *sparseSet) maxSize() int {
	return cap(s.dense)
}

func (s *sparseSet) clear() {
	s.dense = s.dense[:0]
}

func (s *sparseSet) contains(i int) bool {
	if i >= len(s.sparseToDense) {
		return false
	}
	return s.sparseToDense[i] < len(s.dense) && s.dense[s.sparseToDense[i]] == i
}

func (s *sparseSet) insert(i int) {
	if s.contains(i) {
		return
	}
	s.insertNew(i)
}

func (s *sparseSet) insertNew(i int) {
	if i >= len(s.sparseToDense) {
		return
	}
	// There's a CHECK here that size < maxSize...

	s.sparseToDense[i] = len(s.dense)
	s.dense = s.dense[:len(s.dense)+1]
	s.dense[len(s.dense)-1] = i
}

type workq struct {
	s           sparseSet
	n           int  // size excluding marks
	maxm        int  // maximum number of marks
	nextm       int  // id of next mark
	lastWasMark bool // last inserted was mark
}

func newWorkq(n, maxmark int) *workq {
	return &workq{
		s:           makeSparseSet(n + maxmark),
		n:           n,
		maxm:        maxmark,
		nextm:       n,
		lastWasMark: true,
	}
}

func (q *workq) isMark(i int) bool { return i >= q.n }

func (q *workq) clear() {
	q.s.clear()
	q.nextm = q.n
}

func (q *workq) contains(i int) bool {
	return q.s.contains(i)
}

func (q *workq) maxmark() int {
	return q.maxm
}

func (q *workq) mark() {
	if q.lastWasMark {
		return
	}
	q.lastWasMark = false
	q.s.insertNew(int(q.nextm))
	q.nextm++
}

func (q *workq) size() int {
	return q.n + q.maxm
}

func (q *workq) insert(id int) {
	if q.s.contains(id) {
		return
	}
	q.insertNew(id)
}

func (q *workq) insertNew(id int) {
	q.lastWasMark = false
	q.s.insertNew(id)
}

func (q *workq) elements() []int { // should be []stateInst. Should we convert sparseset to use stateInst instead of int??
	return q.s.dense
}

// -----------------------------------------------------------------------------
// search params

type searchParams struct {
	input input // StringPiece
	rinput rinput
	startpos int
	// text StringPiece
	// context StringPiece
	anchored          bool
	wantEarliestMatch bool
	runForward        bool
	start             *State
	firstbyte         int64 // int64 to be compatible with atomic ops
	cacheLock         sync.Locker
	failed            bool // "out" parameter: whether search gave up
	ep                int  // "out" parameter: end pointer for match

	matches []int
}

// -----------------------------------------------------------------------------
// state set... don't know how to do this right...
// TODO(matloob): implement stateset properly!

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
	/* volatile! */ firstbyte int64
}

// -----------------------------------------------------------------------------
// DFA

type matchKind int

const (
	manyMatch matchKind = iota // TODO(matloob): where's this set?
	firstMatch
	longestMatch
)

type DFA struct {
	// Constant after initialization.
	regexp *Regexp // TODO(matloob): this isn't set yet...
	prog            *syntax.Prog
	kind            matchKind // kind of DFA
	startUnanchored int       // start of unanchored program -- TODO(matloob): create this in compile?
	initFailed      bool      // initialization failed (out of memory) REMOVE THIS FIELD?? TODO(matloob)

	mu sync.Mutex // what does this mean: "mutex_ >= cache_mutex.r"

	//  Scratch areas, protected by mu
	q0, q1 *workq
	astack []int

	cacheMu     sync.Mutex
	memBudget   int64
	stateBudget int64 // is this used?
	bytemap     []int
	stateCache  stateSet
	start       [maxStart]startInfo // should this be a slice?
	
	
	// TODO(matloob): removeme
	reverse bool // is this a reverse DFA?
	divides []int
}

func newDFA(prog *syntax.Prog, kind matchKind, maxMem int64) *DFA {
	d := new(DFA)
	d.prog = prog
	d.computeByteMap()
	d.kind = kind
	d.startUnanchored = 0
	d.initFailed = false // remove initFailed!! TODO(matloob)
	d.memBudget = maxMem

	if DebugDFA {
		fmt.Fprintf(os.Stderr, "\nkind %d\n%v\n", kind, prog)
	}

	nmark := 0
	// A note on startUnanchored.
	// To support unanchored searches in RE2, the prog will have a .* put at
	// the location startUnanchored, patched to the actual regexp start.
	// We don't do that here.
	if kind == longestMatch {
		nmark = len(prog.Inst)
		d.startUnanchored = prog.StartUnanchored
	}
	nastack := 2*len(prog.Inst) + nmark

	for i := range d.start {
		d.start[i].firstbyte = fbUnknown
	}

	// Account for space needed for DFA, q0, q1, astack.
	/* TODO(matloob): DO state memory budget stuff */
	d.stateBudget = d.memBudget

	d.q0 = newWorkq(len(prog.Inst), nmark)
	d.q1 = newWorkq(len(prog.Inst), nmark)
	d.astack = make([]int, nastack)

	return d
}

func newReverseDFA(prog *syntax.Prog, kind matchKind, maxMem int64) *DFA {
	d := newDFA(prog, kind, maxMem)
	d.reverse = true
	return d
}

func (d *DFA) search(i input, startpos int, reversed *DFA) (int, int, bool) {
	params := searchParams{}
	params.startpos = startpos
	params.wantEarliestMatch = false
	params.input = i
	params.runForward = true
	params.ep = int(math.MaxInt64)
	if !d.analyzeSearch(&params) {
		panic("analyzesearch failed")
		return -1, -1, false
	}
	b := d.slowSearchLoop(&params)
	if !b {
		return -1, -1, false
	}
	end := params.ep

	params = searchParams{}
	params.startpos = startpos
	params.ep = end
	params.anchored = true
	// params.wantEarliestMatch = true
	params.input = i
	params.rinput= reverse(i)
	params.runForward = false
	if !reversed.analyzeSearch(&params) {
		return -2, -2, false
	}
	b = reversed.slowSearchLoop(&params)
	return params.ep, end, b
}

// BuildAllStates
func (d *DFA) BuildAllStates() int {
	// if !ok() { return 0; }

	// Pick out start state for unanchored search at beginning of text.
	// d.cacheMutex.Lock()
	params := searchParams{ input: &inputString{""} /* null, null, lock */ }
	params.anchored = true
	if d.prog.StartUnanchored != 0 {
		// XXX better check here
		params.anchored = false
	}
	if !d.analyzeSearch(&params) || isSpecialState(params.start) {
		return 0
	}

	// Add start state to work queue.
	queued := stateSet{}
	queued.insert(params.start)
	q := []*State{params.start}

	// Flood to expand every state.
	for i := 0; i < len(q); i++ {
		s := q[i]
		for c := 0; c < 256; c++ {
			ns := d.runStateOnByteUnlocked(s, c)
			if !isSpecialState(ns) && queued.find(ns) == nil {
				queued.insert(ns)
				q = append(q, ns)
			}
		}
	}

	return len(q)
}

func (d *DFA) analyzeSearch(params *searchParams) bool {
	input := params.input

	// Sanity check: make sure that text lies within context
	// TODO(matloob): is this necessary?

	// Determine correct search type.
	// TODO(matloob): set start and flags
	var start int
	var flags flag
	if params.runForward {
		flags =  flag(input.context(params.startpos))
	} else {
		flags = flag(params.rinput.context(params.ep))
		// reverse the flag -- do this a nicer way!
		flags = flag(int(flags) & ^0xF) |((flags & 0xA) >> 1) | ((flags & 0x5) << 1)
	}
	
	if flags & flag(syntax.EmptyBeginText) != 0{
		start |= startBeginText
	} else if flags & flag(syntax.EmptyBeginLine) != 0 {
		start |= startBeginLine
	} else if flags & flag(syntax.EmptyWordBoundary) != 0 {
		start |= startWordBoundary
	} else {
		start |= startNonWordBoundary
	}
	if params.anchored /* || prog.anchorStart() */ {
		start |= kStartAnchored
	}
	info := d.start[start]

	if !d.analyzeSearchHelper(params, &info, flags) {
		panic("failed to analyze start state") // LOG(DFATAL)
		params.failed = true
		return false
	}

	if DebugDFA {
		var fb int
		_ = fb
		/*
		   ATOMIC_LOAD_RELAXED(fb, &info->firstbyte);
		   fprintf(stderr, "anchored=%d fwd=%d flags=%#x state=%s firstbyte=%d\n",
		           params->anchored, params->run_forward, flags,
		           DumpState(info->start).c_str(), fb);
		*/
	}

	params.start = info.start
	params.firstbyte = atomic.LoadInt64(&info.firstbyte) // is this correct?
	//   ATOMIC_LOAD_ACQUIRE(params->firstbyte, &info->firstbyte);

	return true
}

func (d *DFA) analyzeSearchHelper(params *searchParams, info *startInfo, flags flag) bool {
	// Quick check;
	fb := atomic.LoadInt64(&info.firstbyte) // another ATOMIC_LOAD_ACQUIRE
	if fb != fbUnknown {
		return true
	}

	d.mu.Lock()
	defer d.mu.Unlock()
	if info.firstbyte != fbUnknown {
		return true
	}

	d.q0.clear()
	s := d.prog.Start
	if !params.anchored {
		s = d.startUnanchored
	}
	d.addToQueue(d.q0, s, flags)
	info.start = d.workqToCachedState(d.q0, flags)
	if info.start == nil {
		log.Print("workq to cached state returned nil!")
		return false
	}

	if info.start == deadState {
		// Synchronize with "quick check" above.
		// ATOMIC_STORE_RELEASE(&info->firstbyte, kFbNone);
		return true
	}

	if info.start == fullMatchState {
		// Synchronize with "quick check" above.
		// ATOMIC_STORE_RELEASE(&info->firstbyte, kFbNone);  // will be ignored
		return true
	}

	// Compute info->firstbyte by running state on all
	// possible byte values, looking for a single one that
	// leads to a different state.
	firstbyte := fbNone
	for i := 0; i < 256; i++ {
		s := d.runStateOnByte(info.start, i)
		if s == nil {
			// Synchronize with "quick check" above.
			// ATOMIC_STORE_RELEASE(&info->firstbyte, kFbNone);
			return false
		}
		if s == info.start {
			continue
		}
		if firstbyte == fbNone {
			firstbyte = i // ... first one
		} else {
			firstbyte = fbMany
			break
		}
	}

	// Synchronize with "quick check" above.
	// ATOMIC_STORE_RELEASE(&info->firstbyte, kFbNone);
	return true

}

// Processes input byte c in state, returning new state.
// Caller does not hold mutex.
func (d *DFA) runStateOnByteUnlocked(state *State, c int) *State {
	d.mu.Lock()
	defer d.mu.Unlock()
	return d.runStateOnByte(state, c)
}



// Looks up bytes in d.bytemap but handles case c == kByteEndText too.
func (d *DFA) byteMap(c int) int {
	// Use the trivial byte map for now...
	// See ComputeByteMap
	if c == int(endOfText) {
		return len(d.divides);
	}
	if c == int(startOfText) {
		return len(d.divides) + 1
	}
	if c > 255 {
		lo, hi := 0, len(d.divides)
		for {
			// search d.divides
			center := (lo+hi)/2
			if center == lo {
				return lo
			}
			divcenter := d.divides[center]
			if c >= divcenter {
				lo = center
			} else {
				hi = center
			}
		}
	}
	return d.bytemap[c]
}

func (d *DFA) computeByteMap() {
	divides := make(map[rune]bool)
	for _, inst := range d.prog.Inst {
		switch inst.Op {
		// Do we need something for the empty width tstuff?
		case syntax.InstRune:
			for i := 0; i < len(inst.Rune); i += 2 {
				divides[inst.Rune[i]] = true
				if i+1 < len(inst.Rune) {
				divides[inst.Rune[i+1] + 1] = true
				}
			}
		case syntax.InstRune1:
			divides[inst.Rune[0]] = true
			divides[inst.Rune[0] + 1]  = true
		case syntax.InstRuneAnyNotNL: 
			divides['\n'] = true
			divides['\n'+1] = true
		}

	}
	
	divl := make([]int, 0,len(divides))
	divl = append(divl, -1)
	for i := range divides {
		divl = append(divl, int(i))
	}
	sort.Ints(divl)
	d.divides = divl
	d.bytemap = make([]int, 256)
	k := 0
	for i := range d.bytemap {
		if divides[rune(i)] {
			k++
		}
		d.bytemap[i] = k
	}
/*	fmt.Println(d.bytemap)
	
	bytemap2 := make([]int, 256)
	for i := range bytemap2 {
		bytemap2[i] = d.byteMap(i)
	}
	fmt.Println(bytemap2)	*/
}

// Processes input byte c in state, returning new state.
func (d *DFA) runStateOnByte(state *State, c int) *State {
	if isSpecialState(state) {
		if state == fullMatchState {
			// It is convenient for routines like PossibleMatchRange
			// if we implement RunStateOnByte for FullMatchState:
			// once you get into this state you never get out,
			// so it's pretty easy.
			return fullMatchState
		}
		if state == deadState {
			panic("dead state in runStateOnByte") // DFATAL
		}
		if state == nil {
			panic("nil state in runStateOnByte") // DFATAL
		}
		panic("unexpected special state in runStateOnByte") // DFATAL
	}

	// If someone else already computed this, return it.
	var ns *State
	if !(d.byteMap(c) < len(state.next)) {
		log.Panicf("d.byteMap(c) > len(state.next)... %d > %d", d.byteMap(c), len(state.next))
	}
	ns = state.next[d.byteMap(c)]
	// ATOMIC_LOAD_CONSUME TODO(matloob): fix this
	if ns != nil {
		return ns
	}
	// Convert state to workq.
	d.stateToWorkq(state, d.q0)

	// Flags marking the kinds of empty-width things (^ $ etc)
	// around this byte.  Before the byte we have the flags recorded
	// in the State structure itself.  After the byte we have
	// nothing yet (but that will change: read on).
//	var needflag, beforeflag, oldbeforeflag, afterflag flag
	
	// Flags marking the kinds of empty-width things (^ $ etc)
	// around this byte.  Before the byte we have the flags recorded
	// in the State structure itself.  After the byte we have
	// nothing yet (but that will change: read on).
	needflag := state.flag >> flagNeedShift 
	beforeflag := state.flag & flagEmptyMask
	oldbeforeflag := beforeflag
	afterflag := flag(0)

	if c == '\n' {
		// Insert implicit $ and ^ around \n
		beforeflag |= flag(syntax.EmptyEndLine)
		afterflag |= flag(syntax.EmptyBeginLine)
	}

	if c == int(endOfText) {
	// Insert implicit $ and \z before the fake "end text" byte.
		beforeflag |= flag(syntax.EmptyEndLine) | flag(syntax.EmptyEndText)
	} else if c == int(startOfText) {
		beforeflag |= flag(syntax.EmptyBeginLine) | flag(syntax.EmptyBeginText)	
	}	

	// The state flag kFlagLastWord says whether the last
	// byte processed was a word character.  Use that info to
	// insert empty-width (non-)word boundaries.
	var islastword bool
	if state.flag&flagLastWord != 0 { // TODO(matloob): better way of setting bool val?
		islastword = true
	}
	isword := c != int(endOfText) && c != int(startOfText) && syntax.IsWordChar(rune(c))
	// HACK(matloob): is it ok to runify c before passing it to IsWordChar?
	if isword == islastword {
		beforeflag |= flag(syntax.EmptyNoWordBoundary)
		
	} else {
		beforeflag |= flag(syntax.EmptyWordBoundary)
	}
	

	// Okay, finally ready to run.
	// Only useful to rerun on empty string if there are new, useful flags.
	if beforeflag & ^oldbeforeflag & needflag != 0 {
		d.runWorkqOnEmptyString(d.q0, d.q1, beforeflag)
		d.q0, d.q1 = d.q1, d.q0
	}
	ismatch := false
	d.runWorkqOnByte(d.q0, d.q1, c, afterflag, &ismatch, d.kind)

	// Most of the time, we build the state from the output of
	// RunWorkqOnByte, so swap q0_ and q1_ here.  However, so that
	// RE2::Set can tell exactly which match instructions
	// contributed to the match, don't swap if c is kByteEndText.
	// The resulting state wouldn't be correct for further processing
	// of the string, but we're at the end of the text so that's okay.
	// Leaving q0_ alone preseves the match instructions that led to
	// the current setting of ismatch.
	if (c != int(endOfText) && c != int(startOfText)) || d.kind != manyMatch {
		d.q0, d.q1 = d.q1, d.q0
	}

	flag := afterflag
	if ismatch {
		flag |= flagMatch // This conversion to empty op is surely wrong!
	}
	if isword {
		flag |= flagLastWord // DITTO!
	}

	ns = d.workqToCachedState(d.q0, flag)

	// Flush ns before linking to it.
	// Write barrier before updating state->next_ so that the
	// main search loop can proceed without any locking, for speed.
	// (Otherwise it would need one mutex operation per input byte.)

	// TODO(matloob): HANDLE THIS!!!!!!!

	// THIS NEEDS TO BE ATOMIC!
	state.next[d.byteMap(c)] = ns
	// ATOMIC_STORE_RELEASE(&state->next_[ByteMap(c)], ns);

	return ns
}

// Looks in the State cache for a State matching q, flag.
// If one is found, returns it.  If one is not found, allocates one,
// inserts it in the cache, and returns it.
func (d *DFA) workqToCachedState(q *workq, flags flag) *State {
	// if DEBUG_MODE { d.mu.AssertHeld() }

	// Construct array of instruction ids for the new state.
	// Only ByteRange, EmptyWidth, and Match instructions are useful to keep:
	// those are the only operators with any effect in
	// RunWorkqOnEmptyString or RunWorkqOnByte.

	ids := make([]int, q.size()) // should we have a sync.pool of these?
	n := 0
	needflags := flag(0) // flags needed by InstEmptyWidth instructions
	sawmatch := false    // whether queue contains guaranteed InstMatch
	sawmark := false     // whether queue contains a mark
	if DebugDFA {
		fmt.Fprintf(os.Stderr, "WorkqToCachedState %s [%x]", dumpWorkq(q), flags)
	}
	for i, id := range q.elements() {
		if sawmatch && (d.kind == firstMatch || q.isMark(id)) {
			break
		}
		if q.isMark(id) {
			if n > 0 && ids[n-1] != int(mark) {
				sawmark = true
				ids[n] = int(mark) // TODO(matloob): handle another int(mark)
				n++
			}
			continue
		}
		inst := d.prog.Inst[id]
		switch inst.Op {
		case syntax.InstAltMatch:
			// This state will continue to a match no matter what
			// the rest of the input is.  If it is the highest priority match
			// being considered, return the special FullMatchState
			// to indicate that it's all matches from here out.
			if d.kind != manyMatch &&
				(d.kind != firstMatch ||
					(i == 0 && greedy(inst, d.prog))) && // greedy?? dfa.cc:639
				(d.kind != longestMatch || !sawmark) &&
				(flags&flagMatch != 0) { // TODO(matloob): another conversion
				// delete[] ids
				if DebugDFA {
					fmt.Fprintf(os.Stderr, " -> FullMatchState\n")
				}
				return fullMatchState
			}
			fallthrough
		case syntax.InstRune, syntax.InstRune1, syntax.InstRuneAny, syntax.InstRuneAnyNotNL,
			syntax.InstEmptyWidth, syntax.InstMatch, // These are useful.
			syntax.InstAlt: //  Not useful, but necessary [*]
			ids[n] = id
			n++
			if inst.Op == syntax.InstEmptyWidth {
				needflags |= flag(inst.Arg)
			}
			if inst.Op == syntax.InstMatch && false /* prog.anchorEnd */ {
				sawmatch = true
			}

		default: // The rest are not.
			break
		}
		// [*] kInstAlt would seem useless to record in a state, since
		// we've already followed both its arrows and saved all the
		// interesting states we can reach from there.  The problem
		// is that one of the empty-width instructions might lead
		// back to the same kInstAlt (if an empty-width operator is starred),
		// producing a different evaluation order depending on whether
		// we keep the kInstAlt to begin with.  Sigh.
		// A specific case that this affects is /(^|a)+/ matching "a".
		// If we don't save the kInstAlt, we will match the whole "a" (0,1)
		// but in fact the correct leftmost-first match is the leading "" (0,0).

	}
	// DCHECK_LE(n, q.size())
	if n > 0 && ids[n-1] == int(mark) {
		n--
	}

	// If there are no empty-width instructions waiting to execute,
	// then the extra flag bits will not be used, so there is no
	// point in saving them.  (Discarding them reduces the number
	// of distinct states.)
	if needflags == 0 {
		flags &= flagMatch
	}

	// NOTE(rsc): The code above cannot do flag &= needflags,
	// because if the right flags were present to pass the current
	// kInstEmptyWidth instructions, new kInstEmptyWidth instructions
	// might be reached that in turn need different flags.
	// The only sure thing is that if there are no kInstEmptyWidth
	// instructions at all, no flags will be needed.
	// We could do the extra work to figure out the full set of
	// possibly needed flags by exploring past the kInstEmptyWidth
	// instructions, but the check above -- are any flags needed
	// at all? -- handles the most common case.  More fine-grained
	// analysis can only be justified by measurements showing that
	// too many redundant states are being allocated.

	// If there are no Insts in the list, it's a dead state,
	// which is useful to signal with a special pointer so that
	// the execution loop can stop early.  This is only okay
	// if the state is *not* a matching state.
	if n == 0 && flags == 0 {
		// delete[] inst
		if DebugDFA {
			fmt.Fprint(os.Stderr, " -> DeadState\n")
		}
		return deadState
	}

	// Reslice ids to contain only the parts we need.
	ids = ids[:n]

	// If we're in longest match mode, the state is a sequence of
	// unordered state sets separated by Marks.  Sort each set
	// to canonicalize, to reduce the number of distinct sets stored.
	if d.kind == longestMatch {
		i := 0 // ids[i:markp] will contain each set
		for i < len(ids) {
			markp := i // markIdx?
			for markp < len(ids) && ids[markp] != int(mark) {
				markp++
			}
			sort.Ints(ids[i:markp])
			if markp < len(ids) {
				markp++
			}
			i = markp
		}
	}

	// Save the needed empty-width flags in the top bits for use later.
	flags |= needflags << flagNeedShift
	state := d.cachedState(ids, flags)
	/* delete[] ids */
	return state
}

// see dfa.cc:639
func greedy(syntax.Inst, *syntax.Prog) bool {
	panic("not implemented")
}

// ids is a list of indexes into prog.Inst
func (d *DFA) cachedState(ids []int, flags flag) *State {
	// if DEBUG_MODE { d.mu.assertHeld() }

	// Look in the cache for a pre-existing state.
	stateKey := State{ids, flags, nil}
	f := d.stateCache.find(&stateKey)
	if f != nil {
		if DebugDFA {
			fmt.Fprintf(os.Stderr, " -cached-> %s\n", dumpState(f))
		}
		return f
	}

	// TODO(matloob): state cache hash table comment not accurate!!!
	// Must have enough memory for new state.
	// In addition to what we're going to allocate,
	// the state cache hash table seems to incur about 32 bytes per
	// *State, empirically.
	// TODO(matloob): COMPLETELY IGNORING MEM BUDGET WARNING!!!

	// Allocate new state, along with room for next and inst.
	// TODO(matloob): this code does a bunch of UNSAFE stuff...

	state := &State{ids, flags, make([]*State, len(d.divides)+2)}
	d.stateCache.insert(state)
	return state
}

// Adds ip to the work queue, following empty arrows according to flag
// and expanding kInstAlt instructions (two-target gotos).
func (d *DFA) addToQueue(q *workq, id int, flags flag) {
	stk := d.astack
	nstk := 0 // TODO(matloob): reslice the stack and use len(stk) instead of nstk??

	stk[nstk] = id
	nstk++

	for nstk > 0 {
		// DCHECK_LE(nstk, nastack)
		nstk--
		id = stk[nstk]

		if id == int(mark) {
			q.mark()
			continue
		}

		if id == 0 {
			continue
		}

		// If ip is already on the queue, nothing to do.
		// Otherwise add it.  We don't actually keep all the ones
		// that get added -- for example, kInstAlt is ignored
		// when on a work queue -- but adding all ip's here
		// increases the likelihood of q->contains(id),
		// reducing the amount of duplicated work.
		if q.contains(id) {
			continue
		}
		q.insertNew(id)

		// Process instruction.
		inst := d.prog.Inst[id]
		switch inst.Op {
		case syntax.InstFail: // can't happen: discarded above
			break
		case syntax.InstRune, syntax.InstRune1, syntax.InstRuneAny, syntax.InstRuneAnyNotNL, syntax.InstMatch: // just save these on the queue
			break
		case syntax.InstCapture, syntax.InstNop:
			stk[nstk] = int(inst.Out)
			nstk++

		case syntax.InstAlt, syntax.InstAltMatch: // two choices: expand both, in order
			stk[nstk] = int(inst.Arg)
			nstk++
			if q.maxmark() > 0 && id == d.startUnanchored && id != d.prog.Start {
				stk[nstk] = int(mark)
				nstk++
			}
			stk[nstk] = int(inst.Out)
			nstk++
			break

		case syntax.InstEmptyWidth:
			empty := flag(inst.Arg)
			if empty&flags == empty { // TODO(matloob): REEXAMINE ME!
				stk[nstk] = int(inst.Out)
				nstk++
			}
			break
		}
	}

}

func (d *DFA) stateToWorkq(s *State, q *workq) {
	q.clear()
	for i := range s.inst {
		if s.inst[i] == int(mark) {
			q.mark()
		} else {
			q.insertNew(int(s.inst[i]))
		}
	}
}

func (d *DFA) runWorkqOnEmptyString(oldq *workq, newq *workq, flag flag) {
	newq.clear()
	for _, si /* name it inst?? */ := range oldq.elements() {
		if oldq.isMark(si) {
			d.addToQueue(newq, int(mark), flag)
		} else {
			d.addToQueue(newq, si, flag)
		}
	}
}

// Runs a Workq on a given byte followed by a set of empty-string flags,
// producing a new Workq in nq.  If a match instruction is encountered,
// sets *ismatch to true.
// L >= mutex_
//
// Runs the work queue, processing the single byte c followed by any empty
// strings indicated by flag.  For example, c == 'a' and flag == kEmptyEndLine,
// means to match c$.  Sets the bool *ismatch to true if the end of the
// regular expression program has been reached (the regexp has matched).
func (d *DFA) runWorkqOnByte(oldq *workq, newq *workq, c int, flag flag,
	ismatch *bool, kind matchKind) {
	// if DEBUG_MODE { d.mu.assertHeld() }

	newq.clear()
	for _, id := range oldq.elements() {
		if oldq.isMark(id) {
			if *ismatch {
				return
			}
			newq.mark()
			continue
		}
		inst := d.prog.Inst[id]
		switch inst.Op {
		case syntax.InstFail: // never succeeds
		case syntax.InstCapture: // already followed
		case syntax.InstNop: // already followed
		case syntax.InstAlt: // already followed
		case syntax.InstAltMatch: // already followed
		case syntax.InstEmptyWidth: // already followed
			break

			// TODO(matloob): do we want inst.op() to merge the cases?
		case syntax.InstRune, syntax.InstRune1, syntax.InstRuneAny, syntax.InstRuneAnyNotNL:
			// THIS USUALLY WON'T WORK
			// TODO(matloob): FIX FIX FIX
			if inst.MatchRune(rune(c)) { // RUNE INT32 eek
				d.addToQueue(newq, int(inst.Out), flag) // TODO,HACK(matloob): why are we converting uint32 to int?
			}
			break

		case syntax.InstMatch:
			if /* prog.anchorEnd && !atendoftext TODO(matloob): THIS */ false {
				break
			}
			*ismatch = true
			if kind == firstMatch {
				return
			}
			break
		}
	}

	if DebugDFA {
		fmt.Fprintf(os.Stderr, "%s on %d[%x] -> %s [%v]\n",
			dumpWorkq(oldq), c, flag, dumpWorkq(newq), *ismatch)
	}

}

func dumpWorkq(q *workq) string {
	var buf bytes.Buffer
	sep := ""
	for _, v := range q.elements() {
		if q.isMark(v) {
			fmt.Fprint(&buf, "|")
			sep = ""
		} else {
			fmt.Fprintf(&buf, "%s%d", sep, v)
			sep = ","
		}
	}
	return buf.String()
}

//////////////////////////////////////////////////////////////////////
//
// DFA execution.
//
// The basic search loop is easy: start in a state s and then for each
// byte c in the input, s = s->next[c].
//
// This simple description omits a few efficiency-driven complications.
//
// First, the State graph is constructed incrementally: it is possible
// that s->next[c] is null, indicating that that state has not been
// fully explored.  In this case, RunStateOnByte must be invoked to
// determine the next state, which is cached in s->next[c] to save
// future effort.  An alternative reason for s->next[c] to be null is
// that the DFA has reached a so-called "dead state", in which any match
// is no longer possible.  In this case RunStateOnByte will return NULL
// and the processing of the string can stop early.
//
// Second, a 256-element pointer array for s->next_ makes each State
// quite large (2kB on 64-bit machines).  Instead, dfa->bytemap_[]
// maps from bytes to "byte classes" and then next_ only needs to have
// as many pointers as there are byte classes.  A byte class is simply a
// range of bytes that the regexp never distinguishes between.
// A regexp looking for a[abc] would have four byte ranges -- 0 to 'a'-1,
// 'a', 'b' to 'c', and 'c' to 0xFF.  The bytemap slows us a little bit
// but in exchange we typically cut the size of a State (and thus our
// memory footprint) by about 5-10x.  The comments still refer to
// s->next[c] for simplicity, but code should refer to s->next_[bytemap_[c]].
//
// Third, it is common for a DFA for an unanchored match to begin in a
// state in which only one particular byte value can take the DFA to a
// different state.  That is, s->next[c] != s for only one c.  In this
// situation, the DFA can do better than executing the simple loop.
// Instead, it can call memchr to search very quickly for the byte c.
// Whether the start state has this property is determined during a
// pre-compilation pass, and if so, the byte b is passed to the search
// loop as the "firstbyte" argument, along with a boolean "have_firstbyte".
//
// Fourth, the desired behavior is to search for the leftmost-best match
// (approximately, the same one that Perl would find), which is not
// necessarily the match ending earliest in the string.  Each time a
// match is found, it must be noted, but the DFA must continue on in
// hope of finding a higher-priority match.  In some cases, the caller only
// cares whether there is any match at all, not which one is found.
// The "want_earliest_match" flag causes the search to stop at the first
// match found.
//
// Fifth, one algorithm that uses the DFA needs it to run over the
// input string backward, beginning at the end and ending at the beginning.
// Passing false for the "run_forward" flag causes the DFA to run backward.
//
// The checks for these last three cases, which in a naive implementation
// would be performed once per input byte, slow the general loop enough
// to merit specialized versions of the search loop for each of the
// eight possible settings of the three booleans.  Rather than write
// eight different functions, we write one general implementation and then
// inline it to create the specialized ones.
//
// Note that matches are delayed by one byte, to make it easier to
// accomodate match conditions depending on the next input byte (like $ and \b).
// When s->next[c]->IsMatch(), it means that there is a match ending just
// *before* byte c.

// The generic search loop.  Searches text for a match, returning
// the pointer to the end of the chosen match, or NULL if no match.
// The bools are equal to the same-named variables in params, but
// making them function arguments lets the inliner specialize
// this function to each combination (see two paragraphs above).
// TODO(matloob): I don't think this can be inlined... we might have
//                to change the name
func (d *DFA) inlinedSearchLoop(params *searchParams, haveFirstbyte, wantEarliestMatch, runForward bool) bool {
	start := params.start
	bp := 0 // start of text
	p := params.startpos  // text scanning point
	ep := params.ep
	if !runForward {
//		fmt.Println("not run forward", p, ep, start)
		p, ep = ep, p 
	} 
	
	// const uint8* byte

	_, _, _, _ = start, bp, p, ep

	// const uint8* bytemap = prog_->bytemap()
	var lastMatch int = -1 // most recent matching position in text
	matched := false
	s := start

	if s.isMatch() { 
		matched = true
		lastMatch = p
		if wantEarliestMatch {
			params.ep = lastMatch
			return true
		}
	}

	var w int
	for p != ep {
//		fmt.Println(".")
		if DebugDFA {
			fmt.Fprintf(os.Stderr, "@%d: %s\n", p - bp, s.Dump())
		}
		if haveFirstbyte && s == start {
			// TODO(matloob): Correct the comment
			// In start state, only way out is to find firstbyte,
			// so use optimized assembly in memchr to skip ahead.
			// If firstbyte isn't found, we can skip to the end
			// of the string.
			if runForward {
				p = params.input.index(d.regexp, p)
				if p < 0 {
					p = ep
					break
				}
			} else {
				panic(" not handled... reverse index !" )
				// p = params.input.rindex(d.regexp, ep)
				if p < 0 {
					p = ep
					break
				}
				p++
			}
		}

		var c int
		if runForward {
			var r rune
			r, w = params.input.step(p)
//			fmt.Println("? ", r)
			c = int(r)
			p += w
		} else {
			var r rune
			r, w = params.rinput.rstep(p)
//			fmt.Println("> ", r, w)
			c = int(r)
			p -= w
		}
		if c == int(endOfText)  { // TODO(matloob): end of text
			break
		}

		// Note that multiple threads might be consulting
		// s->next_[bytemap[c]] simultaneously.
		// RunStateOnByte takes care of the appropriate locking,
		// including a memory barrier so that the unlocked access
		// (sometimes known as "double-checked locking") is safe.
		// The alternative would be either one DFA per thread
		// or one mutex operation per input byte.
		//
		// ns == DeadState means the state is known to be dead
		// (no more matches are possible).
		// ns == NULL means the state has not yet been computed
		// (need to call RunStateOnByteUnlocked).
		// RunStateOnByte returns ns == NULL if it is out of memory.
		// ns == FullMatchState means the rest of the string matches.
		//
		// Okay to use bytemap[] not ByteMap() here, because
		// c is known to be an actual byte and not kByteEndText.
		var ns *State
//		fmt.Println("next", len(s.next))
		// ATOMIC_LOAD_CONSUME(ns, &s->next_[bytemap[c]]);
		ns = s.next[d.byteMap(c)]
		if ns == nil {
			ns = d.runStateOnByteUnlocked(s, c)
			if ns == nil {
				panic("state saving stuff not implemented")
			}
			/*
				ns = RunStateOnByteUnlocked(s, c);
				if (ns == NULL) {
				  // After we reset the cache, we hold cache_mutex exclusively,
				  // so if resetp != NULL, it means we filled the DFA state
				  // cache with this search alone (without any other threads).
				  // Benchmarks show that doing a state computation on every
				  // byte runs at about 0.2 MB/s, while the NFA (nfa.cc) can do the
				  // same at about 2 MB/s.  Unless we're processing an average
				  // of 10 bytes per state computation, fail so that RE2 can
				  // fall back to the NFA.
				  if (FLAGS_re2_dfa_bail_when_slow && resetp != NULL &&
				      (p - resetp) < 10*state_cache_.size()) {
				    params->failed = true;
				    return false;
				  }
				  resetp = p;
		
				  // Prepare to save start and s across the reset.
				  StateSaver save_start(this, start);
				  StateSaver save_s(this, s);
		
				  // Discard all the States in the cache.
				  ResetCache(params->cache_lock);
		
				  // Restore start and s so we can continue.
				  if ((start = save_start.Restore()) == NULL ||
				      (s = save_s.Restore()) == NULL) {
				    // Restore already did LOG(DFATAL).
				    params->failed = true;
				    return false;
				  }
				  ns = RunStateOnByteUnlocked(s, c);
				  if (ns == NULL) {
				    LOG(DFATAL) << "RunStateOnByteUnlocked failed after ResetCache";
				    params->failed = true;
				    return false;
				  }
				}
			*/
	
		}
	
		//  if (ns <= SpecialStateMax) {
		if isSpecialState(ns) {
			if ns == deadState {
//				fmt.Println("deadstate")
				params.ep = lastMatch
				return matched
			}
			params.ep = ep
			return true
		}
		s = ns
	
		if s.isMatch() {
			matched = true
			// The DFA notices the match one rune late,
			// so adjust p before using it in the match.
			if runForward {
				lastMatch = p - w
			} else {
				lastMatch = p + w
			}
			if DebugDFA {
				fmt.Fprintf(os.Stderr, "match @%d! [%s]\n", lastMatch - bp, s.Dump())
			}
			if wantEarliestMatch {
				params.ep = lastMatch
				return true
			}
		}
	}

	// Process one more byte to see if it triggers a match.
	// (Remember, matches are delayed one byte.)
	var lastbyte int // TODO(matloob): not really a byte...
	if runForward {
		// TODO(matloob): fix
		lastbyte = int(endOfText)
		/*
		if (params->text.end() == params->context.end())
	  		lastbyte = kByteEndText;
	  	else
	  		lastbyte = params->text.end()[0] & 0xFF;
		*/
	} else {
		lastbyte = int(endOfText)
		/*
		if (params->text.begin() == params->context.begin())
			lastbyte = kByteEndText;
		else
			lastbyte = params->text.begin()[-1] & 0xFF;
		*/
	}


//	fmt.Println(s.Dump())
//	fmt.Println(s.next)
	var ns *State
	// ATOMIC_LOAD_CONSUME(ns, &s->next_[ByteMap(lastbyte)]);
	// TODO(matloob): ATOMIC
	ns = s.next[d.byteMap(lastbyte)]
	if ns == nil {
		ns = d.runStateOnByteUnlocked(s, lastbyte)
		if ns == nil {
			panic("state saver stuff NOT implemented")
		}
/*
		ns = RunStateOnByteUnlocked(s, lastbyte);
		if (ns == NULL) {
			StateSaver save_s(this, s);
			ResetCache(params->cache_lock);
			if ((s = save_s.Restore()) == NULL) {
				params->failed = true;
				return false;
			}
			ns = RunStateOnByteUnlocked(s, lastbyte);
			if (ns == NULL) {
				LOG(DFATAL) << "RunStateOnByteUnlocked failed after Reset";
				params->failed = true;
				return false;
			}
		}
*/
	}


	s = ns
	if DebugDFA {
		// fprintf(stderr, "@_: %s\n", DumpState(s).c_str());
	}
	if s == fullMatchState {
//		fmt.Println("fullmatch")
		params.ep = ep
		return true
	}
	if !isSpecialState(s) && s.isMatch() {
//		fmt.Println("match")
		matched = true
		lastMatch = p
		// TODO(matloob): Just remove this? Do we support ManyMatch?
		if params.matches != nil && false /* && d.kind == ManyMatch */ {
			v := params.matches
			v = v[:0] // TODO(matloob): just operate on params.matches?
			for i := range s.inst {
				inst := d.prog.Inst[s.inst[i]]
				if inst.Op == syntax.InstMatch {
					v = append(v, 0 /* inst.matchID() */ ) // TODO(matloob): match id?
				}
			}
			params.matches = v
		}
		if DebugDFA {
		//	fprintf(stderr, "match @%d! [%s]\n", static_cast<int>(lastmatch - bp), DumpState(s).c_str());
		}
	}
	params.ep = lastMatch
	return matched
}

// Inline specializations of the general loop.
// TODO(matloob): XXX FIXME
// Go won't inline inlinedSearchLoop, right? Should these be removed or renamed?
func (d *DFA) searchFFF(params *searchParams) bool {
	return d.inlinedSearchLoop(params, false, false, false)
}
func (d *DFA) searchFFT(params *searchParams) bool {
	return d.inlinedSearchLoop(params, false, false, true)
}
func (d *DFA) searchFTF(params *searchParams) bool {
	return d.inlinedSearchLoop(params, false, true, false)
}
func (d *DFA) searchFTT(params *searchParams) bool {
	return d.inlinedSearchLoop(params, false, true, true)
}
func (d *DFA) searchTFF(params *searchParams) bool {
	return d.inlinedSearchLoop(params, true, false, false)
}
func (d *DFA) searchTFT(params *searchParams) bool {
	return d.inlinedSearchLoop(params, true, false, true)
}
func (d *DFA) searchTTF(params *searchParams) bool {
	return d.inlinedSearchLoop(params, true, true, false)
}
func (d *DFA) searchTTT(params *searchParams) bool {
	return d.inlinedSearchLoop(params, true, true, true)
}

// slowSearchLoop calls the general code directly, for debugging.
func (d *DFA) slowSearchLoop(params *searchParams) bool {
	return d.inlinedSearchLoop(params, params.firstbyte >= 0, params.wantEarliestMatch, params.runForward)
}

func (d *DFA) fastSearchLoop(params *searchParams) {
	// TODO(matloob): implement
	d.slowSearchLoop(params)
}
