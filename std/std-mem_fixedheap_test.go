// Why: a FixedHeap hands out and takes back the bytes of one buffer in any
// order, so every placement must be the one its design gives, and the
// tests that say so must be seen to catch a wrong one.
// What: mem.FixedHeap against the Go model of std-mem_heapmodel_test.go
// over seeded tapes, planted bugs that the comparison must see, the loans
// of the four new allocators, their owners, their test blocks and what
// compile-time evaluation makes of them.
// How: one program runs every case, dev and release, and its lines are
// compared with the model's; a plant is the same program built over a copy
// of std with one line of an allocator changed.

package std

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// heapCase is one buffer of the differential test: its length, the offset
// into a stack array (so the address skew varies), and its tape: the seed,
// the number of ops, the largest request, the percentage of allocations,
// and whether resets and wild requests are mixed in.
type heapCase struct {
	name          string
	size, shift   int
	seed          uint64
	ops, maxSize  int
	alloc         int
	resets, wilds bool
}

// heapCases run from no buffer at all, through the sizes around the
// smallest that holds one block (96 bytes from an 8-byte boundary) and the
// sizes on both sides of each change in the number of first levels (the
// "levels" cases), to 64 KiB. A tape with 50 percent allocations fills its
// buffer, so most of its requests meet a full heap; one with 38 keeps it
// half empty and churns.
var heapCases = []heapCase{
	{"empty", 0, 0, 1, 40, 8, 50, true, true},
	{"one", 1, 3, 2, 60, 2, 50, true, true},
	{"under", 88, 1, 3, 120, 16, 50, true, true},
	{"least", 96, 0, 4, 300, 16, 50, true, true},
	{"least-3", 99, 3, 5, 300, 16, 50, true, true},
	{"least-7", 103, 7, 6, 300, 16, 50, true, true},
	{"least-8", 104, 0, 7, 300, 24, 50, true, true},
	{"levels-128", 128, 0, 21, 400, 24, 50, true, true},
	{"levels-152", 152, 5, 22, 400, 40, 50, true, true},
	{"levels-167", 167, 1, 23, 400, 40, 50, true, true},
	{"levels-200", 200, 2, 24, 500, 60, 50, true, true},
	{"levels-248", 248, 0, 25, 500, 90, 50, true, true},
	{"small", 256, 3, 8, 600, 40, 50, true, false},
	{"levels-264", 264, 4, 26, 500, 90, 50, true, true},
	{"levels-504", 504, 0, 27, 800, 200, 48, true, false},
	{"levels-520", 520, 6, 28, 800, 200, 48, true, false},
	{"levels-1016", 1016, 0, 29, 1000, 400, 48, true, false},
	{"k1", 1024, 0, 9, 1200, 100, 45, true, false},
	{"page", 4096, 0, 10, 1500, 300, 50, true, false},
	{"page-skew", 4096, 7, 11, 1500, 300, 50, false, false},
	{"page-churn", 4096, 2, 12, 2500, 120, 38, false, false},
	{"big", 65536, 4, 13, 3000, 300, 50, true, false},
	{"big-large", 65536, 1, 14, 1500, 20000, 45, false, false},
	{"big-churn", 65536, 6, 15, 3000, 2000, 38, false, false},
	{"wild", 512, 3, 16, 1500, 48, 45, true, true},
	{"wild-page", 4096, 6, 17, 2500, 200, 42, false, true},
	{"wild-big", 32768, 5, 18, 2500, 700, 42, true, true},
}

// heapProgram runs every case in one program: each case's buffer is a
// slice of an array of its own, at its shift.
func heapProgram(cases []heapCase) (string, map[string][]int) {
	var b strings.Builder
	b.WriteString("import std.memnew\n\nexport Main(sys: &System): WriteError!void {\n    var out := sys.Stdout()\n")
	ops := map[string][]int{}
	for i, c := range cases {
		wild := memWildNone
		if c.wilds {
			wild = memWildAll
		}
		o := heapOps(c.seed, c.ops, c.maxSize, c.alloc, c.resets, wild)
		ops[c.name] = o
		fmt.Fprintf(&b, "    try Print(mut out, \"case %s\\n\")\n", c.name)
		fmt.Fprintf(&b, "    var buf%d: [%d]u8 = [0; %d]\n", i, c.size+c.shift+1, c.size+c.shift+1)
		fmt.Fprintf(&b, "    ops%d := %s\n", i, mkInts(o))
		fmt.Fprintf(&b, "    try memnew.RunHeap(mut out, mut buf%d[%d..%d], ops%d[..])\n", i, c.shift, c.shift+c.size, i)
	}
	b.WriteString("}\n")
	return b.String(), ops
}

// memSkews reads the "skew a [b]" line that starts a case's output and
// returns the numbers and the rest.
func memSkews(t *testing.T, name, g string) ([]int, string) {
	t.Helper()
	line, rest, _ := strings.Cut(g, "\n")
	var skews []int
	f := strings.Fields(line)
	if len(f) < 2 || f[0] != "skew" {
		t.Fatalf("case %s: no skew line: %q", name, line)
	}
	for _, s := range f[1:] {
		var v int
		if _, err := fmt.Sscan(s, &v); err != nil {
			t.Fatalf("case %s: skew line %q: %v", name, line, err)
		}
		skews = append(skews, v)
	}
	return skews, rest
}

// heapCompare judges one case's output against the model and returns how
// many of its lines are an allocation granted, an allocation refused, a
// resize granted, a resize refused and a free.
func heapCompare(t *testing.T, what string, c heapCase, g string, ops []int) (tally [5]int) {
	t.Helper()
	skews, _ := memSkews(t, c.name, g)
	want := heapExpect(t, skews[0], c.size, ops)
	if g != want {
		t.Errorf("%s case %s (skew %d):", what, c.name, skews[0])
		diffLines(t, g, want)
	}
	for _, l := range strings.Split(g, "\n") {
		switch {
		case l == "a null":
			tally[1]++
		case strings.HasPrefix(l, "a "):
			tally[0]++
		case strings.HasPrefix(l, "r ") && strings.HasSuffix(l, " true"):
			tally[2]++
		case strings.HasPrefix(l, "r "):
			tally[3]++
		case strings.HasPrefix(l, "f "):
			tally[4]++
		}
	}
	return tally
}

// TestSTDMEM_FixedHeapMatchesModel: seeded tapes of allocations (0 to
// 20,000 bytes, alignments 1 to 4096), resizes, frees in any order, resets
// and the requests no container makes, over FixedHeap buffers of 0 to
// 65,536 bytes at several address skews, print exactly the model's
// offsets, dev and release. The model is judged by heapOracle after every
// op, and at the end of each tape every block is freed and the whole
// buffer is one request again. No block's contents change under another
// request. The tapes are also checked to reach what they are for: every
// kind of line many times.
func TestSTDMEM_FixedHeapMatchesModel(t *testing.T) {
	t.Parallel()
	src, ops := heapProgram(heapCases)
	for _, flags := range [][]string{nil, {"--release"}} {
		out := collExec(t, memNewBuild(t, src, flags...))
		if strings.Contains(out, "corrupt") {
			t.Errorf("%v: a block's contents changed under another request:\n%.2000s", flags, out)
		}
		got := splitCases(out)
		var total [5]int
		wholes := 0
		for _, c := range heapCases {
			g, ok := got[c.name]
			if !ok {
				t.Fatalf("%v: no output for case %s\n%.2000s", flags, c.name, out)
			}
			tally := heapCompare(t, fmt.Sprint(flags), c, g, ops[c.name])
			for i, n := range tally {
				total[i] += n
			}
			if strings.Contains(g, "\nwhole ") {
				wholes++
			}
		}
		t.Logf("%v: %d allocations granted, %d refused, %d resizes granted, %d refused, %d frees; %d of %d buffers hold a heap", flags, total[0], total[1], total[2], total[3], total[4], wholes, len(heapCases))
		for i, least := range [5]int{5000, 1000, 1000, 1000, 4000} {
			if total[i] < least {
				t.Errorf("%v: the tapes reach line kind %d only %d times, want at least %d", flags, i, total[i], least)
			}
		}
		if wholes < 22 {
			t.Errorf("%v: only %d buffers hold a heap", flags, wholes)
		}
	}
}

// memPlant is one planted bug: a file of std/mem and a piece of it,
// present exactly once, replaced by another that still compiles.
type memPlant struct {
	name, file, old, new string
}

// heapPlants are wrong FixedHeaps the differential test must tell from the
// real one: each breaks one rule of fixedheap.mk's header.
var heapPlants = []memPlant{
	{"free-keeps-the-block-after-apart", "mem/fixedheap.mk",
		"    if (ns & FhFree) != 0 {\n        FhUnlink(h, nx, ns & FhSize)\n        n = n +% (ns & FhSize)\n    }\n    pv := FhR(b, g << 3)",
		"    if (ns & FhFree) != 0 && n < 0 {\n        FhUnlink(h, nx, ns & FhSize)\n        n = n +% (ns & FhSize)\n    }\n    pv := FhR(b, g << 3)"},
	{"free-keeps-the-block-before-apart", "mem/fixedheap.mk",
		"    if pv != 0 && (FhR(b, ((g -% pv) << 3) +% 4) & FhFree) != 0 {",
		"    if pv < 0 && (FhR(b, ((g -% pv) << 3) +% 4) & FhFree) != 0 {"},
	{"fit-does-not-round-up", "mem/fixedheap.mk",
		"    return FhList(g + (1 << (b - 4)) - 1)",
		"    return FhList(g + (1 << (b - 4)) - (1 << (b - 4)))"},
	{"carve-keeps-a-rest-of-two", "mem/fixedheap.mk",
		"    rest := have -% need\n    if rest < 2 {",
		"    rest := have -% need\n    if rest < 3 {"},
	{"wide-gap-of-one-granule", "mem/fixedheap.mk",
		"    if gap == 1 {\n        gap += ag\n    }",
		"    if gap == 1 {\n        gap += ag - ag\n    }"},
	{"resize-grows-one-granule-short", "mem/fixedheap.mk",
		"            if cur +% (ns & FhSize) < need {",
		"            if cur +% (ns & FhSize) +% 1 < need {"},
	{"resize-shrinks-without-merging", "mem/fixedheap.mk",
		"    if need != cur {\n        nx := g +% cur",
		"    if need > cur {\n        nx := g +% cur"},
	{"second-free-not-refused", "mem/fixedheap.mk",
		"    if (FhR(h.base, (g << 3) +% 4) & FhFree) != 0 {\n        return 0\n    }\n    return g",
		"    if (FhR(h.base, (g << 3) +% 4) & FhFree) != 0 && g < 0 {\n        return 0\n    }\n    return g"},
	{"unaligned-pointer-taken-for-a-block", "mem/fixedheap.mk",
		"    if (off & 7) != 0 || Trunc[uint](g -% h.first) >= Trunc[uint](h.last -% h.first) {",
		"    if (off & 7) > 7 || Trunc[uint](g -% h.first) >= Trunc[uint](h.last -% h.first) {"},
	{"own-list-taken-without-its-size", "mem/fixedheap.mk",
		"    if n < need {\n        return 0\n    }\n    FhUnlink(h, own, n)",
		"    if n < 0 {\n        return 0\n    }\n    FhUnlink(h, own, n)"},
}

// memPlantSource is the file of plant p with its change made; it fails the
// test when the file no longer holds the piece exactly once, so a plant
// cannot go stale unseen.
func memPlantSource(t *testing.T, p memPlant) string {
	t.Helper()
	b, err := os.ReadFile(filepath.FromSlash(p.file))
	if err != nil {
		t.Fatal(err)
	}
	src := strings.ReplaceAll(string(b), "\r\n", "\n")
	if n := strings.Count(src, p.old); n != 1 {
		t.Fatalf("plant %s: std/%s holds its piece %d times, want once:\n%s", p.name, p.file, n, p.old)
	}
	return strings.Replace(src, p.old, p.new, 1)
}

// memRunLoose runs exe and returns its output, and whether it ran to a
// clean exit in time: a planted bug may crash or hang instead of printing
// a wrong line.
func memRunLoose(t *testing.T, exe string) (string, bool) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, exe)
	cmd.Dir = filepath.Dir(exe)
	var out bytes.Buffer
	cmd.Stdout = &out
	err := cmd.Run()
	return out.String(), err == nil && ctx.Err() == nil
}

// TestSTDMEM_FixedHeapPlantsAreSeen: each planted bug, built into a copy
// of std, makes the differential program print something the model does
// not, crash or hang, so the comparison of TestSTDMEM_FixedHeapMatchesModel
// has teeth; the same program over the unchanged std agrees with the
// model, so it is the plant that is seen.
func TestSTDMEM_FixedHeapPlantsAreSeen(t *testing.T) {
	t.Parallel()
	src, ops := heapProgram(heapCases)
	agrees := func(t *testing.T, out string) bool {
		got := splitCases(out)
		for _, c := range heapCases {
			g, ok := got[c.name]
			if !ok || !strings.HasPrefix(g, "skew ") {
				return false
			}
			skews, _ := memSkews(t, c.name, g)
			if g != heapExpect(t, skews[0], c.size, ops[c.name]) {
				return false
			}
		}
		return true
	}
	t.Run("unchanged", func(t *testing.T) {
		t.Parallel()
		out, clean := memRunLoose(t, memNewBuild(t, src))
		if !clean || !agrees(t, out) {
			t.Fatalf("the unchanged std does not agree with the model (clean exit %t)", clean)
		}
	})
	for _, p := range heapPlants {
		t.Run(p.name, func(t *testing.T) {
			t.Parallel()
			root := t.TempDir()
			stdDir := memNewCopyStd(t, root, map[string]string{p.file: memPlantSource(t, p)})
			exe, built := memNewBuildIn(t, root, stdDir, src, true)
			if !built {
				t.Fatalf("plant %s does not compile, so it tests nothing", p.name)
			}
			out, clean := memRunLoose(t, exe)
			if clean && agrees(t, out) {
				t.Errorf("plant %s: the run agrees with the model line for line", p.name)
			}
		})
	}
}

// memNewLoanCases are probe functions over the four new allocators: a
// marked line gets one of its codes, an unmarked function checks clean.
// They pin what the signatures promise: a FixedHeap and a Fallback hold
// their buffer exclusively, a Limit, a Failing and a Fallback hold their
// inner allocator, Reset ends what was allocated, and none is Share.
var memNewLoanCases = []struct {
	name string
	fn   string
	want []string
}{
	{"fixedheap-holds-buf", `A(): int {
    var buf: [256]u8 = [0; 256]
    h := mem.FixedHeap.New(mut buf[..])
    b := Box[int].New(h.Alloc(), 1) else {
        return 0
    }
    x := buf[0] // <-
    b.Free(h.Alloc())
    return Cast[int](x)
}`, []string{"E0504"}},
	{"fixedheap-buf-after", `A2(): int {
    var buf: [256]u8 = [0; 256]
    h := mem.FixedHeap.New(mut buf[..])
    b := Box[int].New(h.Alloc(), 1) else {
        return 0
    }
    b.Free(h.Alloc())
    return Cast[int](buf[0]) + buf[..].Len()
}`, nil},
	{"fixedheap-reset-ends-box", `B() {
    var buf: [256]u8 = [0; 256]
    var h := mem.FixedHeap.New(mut buf[..])
    b := Box[int].New(h.Alloc(), 1) else {
        return
    }
    h.Reset() // <-
    b.Free(h.Alloc())
}`, []string{"E0501"}},
	{"fixedheap-reset-ends-heaplist", `B2() {
    var buf: [256]u8 = [0; 256]
    var h := mem.FixedHeap.New(mut buf[..])
    var xs := HeapList[int].New(h.Alloc())
    h.Reset() // <-
    xs.Free(h.Alloc())
}`, []string{"E0501"}},
	{"fixedheap-reset-after-free", `B3() {
    var buf: [256]u8 = [0; 256]
    var h := mem.FixedHeap.New(mut buf[..])
    b := Box[int].New(h.Alloc(), 1) else {
        return
    }
    b.Free(h.Alloc())
    h.Reset()
    _ = h.Alloc()
}`, nil},
	{"fixedheap-reset-keeps-buf", `B4(): int {
    var buf: [256]u8 = [0; 256]
    var h := mem.FixedHeap.New(mut buf[..])
    h.Reset()
    x := buf[0] // <-
    _ = h.Alloc()
    return Cast[int](x)
}`, []string{"E0504"}},
	{"fixedheap-reset-escapes", `B5(): mem.FixedHeap {
    var buf: [256]u8 = [0; 256]
    var h := mem.FixedHeap.New(mut buf[..])
    h.Reset()
    return h // <-
}`, []string{"E0603"}},
	{"limit-holds-inner", `C(h: &Heap): int {
    var ar := Arena.New(h) else {
        return 0
    }
    l := mem.Limit.New(ar.Alloc(), 64)
    ar.Free() // <-
    return l.Bytes()
}`, []string{"E0503"}},
	{"failing-holds-inner", `D(h: &Heap): int {
    var ar := Arena.New(h) else {
        return 0
    }
    f := mem.Failing.New(ar.Alloc(), 0)
    ar.Free() // <-
    return f.Failed()
}`, []string{"E0503"}},
	{"failing-from-holds-inner", `D2(h: &Heap): int {
    var ar := Arena.New(h) else {
        return 0
    }
    f := mem.Failing.NewFrom(ar.Alloc(), 0)
    ar.Free() // <-
    return f.Requests()
}`, []string{"E0503"}},
	{"fallback-holds-inner", `E(h: &Heap) {
    var buf: [64]u8 = [0; 64]
    var ar := Arena.New(h) else {
        return
    }
    b := mem.Fallback.New(ar.Alloc(), mut buf[..])
    ar.Free() // <-
    _ = b.Alloc()
}`, []string{"E0503"}},
	{"fallback-holds-buf", `E2(h: &Heap): int {
    var buf: [64]u8 = [0; 64]
    b := mem.Fallback.New(h.Alloc(), mut buf[..])
    x := Box[int].New(b.Alloc(), 1) else {
        return 0
    }
    y := buf[0] // <-
    x.Free(b.Alloc())
    return Cast[int](y)
}`, []string{"E0504"}},
	{"fallback-reset-ends-box", `E3(h: &Heap) {
    var buf: [64]u8 = [0; 64]
    var b := mem.Fallback.New(h.Alloc(), mut buf[..])
    x := Box[int].New(b.Alloc(), 1) else {
        return
    }
    b.Reset() // <-
    x.Free(b.Alloc())
}`, []string{"E0501"}},
	{"fallback-reset-after-free", `E4(h: &Heap) {
    var buf: [64]u8 = [0; 64]
    var b := mem.Fallback.New(h.Alloc(), mut buf[..])
    x := Box[int].New(b.Alloc(), 1) else {
        return
    }
    x.Free(b.Alloc())
    b.Reset()
    _ = b.Alloc()
}`, nil},
	{"fallback-reset-keeps-inner", `E5(h: &Heap) {
    var buf: [64]u8 = [0; 64]
    var ar := Arena.New(h) else {
        return
    }
    var b := mem.Fallback.New(ar.Alloc(), mut buf[..])
    b.Reset()
    ar.Free() // <-
    _ = b.Alloc()
}`, []string{"E0503"}},
	{"fallback-reset-keeps-buf", `E6(h: &Heap): int {
    var buf: [64]u8 = [0; 64]
    var b := mem.Fallback.New(h.Alloc(), mut buf[..])
    b.Reset()
    y := buf[0] // <-
    _ = b.Alloc()
    return Cast[int](y)
}`, []string{"E0504"}},
	{"fallback-reset-escapes", `E7(h: &Heap): mem.Fallback {
    var buf: [64]u8 = [0; 64]
    var b := mem.Fallback.New(h.Alloc(), mut buf[..])
    b.Reset()
    return b // <-
}`, []string{"E0603"}},
	{"fixedheap-not-share", `F(x: &mem.FixedHeap): int {
    return G(x) // <-
}

G[T: Share](x: &T): int {
    return 0
}`, []string{"E0701"}},
	{"limit-not-share", `F2(x: &mem.Limit): int {
    return G2(x) // <-
}

G2[T: Share](x: &T): int {
    return 0
}`, []string{"E0701"}},
	{"failing-not-share", `F3(x: &mem.Failing): int {
    return G3(x) // <-
}

G3[T: Share](x: &T): int {
    return 0
}`, []string{"E0701"}},
	{"fallback-not-share", `F4(x: &mem.Fallback): int {
    return G4(x) // <-
}

G4[T: Share](x: &T): int {
    return 0
}`, []string{"E0701"}},
}

// TestSTDMEM_NewAllocLoans: each probe function is checked alone; a marked
// line gets one of its codes and no other line any code, and an unmarked
// function checks clean.
func TestSTDMEM_NewAllocLoans(t *testing.T) {
	t.Parallel()
	for _, c := range memNewLoanCases {
		t.Run(c.name, func(t *testing.T) {
			t.Parallel()
			src := "import std.mem\n\n" + c.fn + "\n\nexport Main(sys: &System) {\n}\n"
			mark := 0
			for i, l := range strings.Split(src, "\n") {
				if strings.HasSuffix(l, "// <-") {
					mark = i + 1
				}
			}
			out, code := memCheck(t, src)
			got := diagCodes(out)
			if c.want == nil {
				if code != 0 || len(got) != 0 {
					t.Errorf("want clean, exit %d\n%s", code, out)
				}
				return
			}
			ok := false
			for _, lc := range got {
				var line int
				var dcode string
				fmt.Sscanf(lc, "%d %s", &line, &dcode)
				if line != mark {
					t.Errorf("unexpected %s at main.mk:%d\n%s", dcode, line, out)
					continue
				}
				for _, w := range c.want {
					ok = ok || dcode == w
				}
			}
			if !ok {
				t.Errorf("main.mk:%d: want one of %v, have %v\n%s", mark, c.want, got, out)
			}
		})
	}
}

// TestSTDMEM_NewAllocSameOwner: Alloc on one FixedHeap, Limit, Failing or
// Fallback returns one owner every call, which the heap containers'
// ownership check relies on, and the four owners differ from each other
// and from the allocator beneath them. Dev and release.
func TestSTDMEM_NewAllocSameOwner(t *testing.T) {
	t.Parallel()
	src := `import std.memnew

export Main(sys: &System): WriteError!void {
    var out := sys.Stdout()
    var buf: [256]u8 = [0; 256]
    var buf2: [64]u8 = [0; 64]
    try Print(mut out, "{s}\n", (s: memnew.SameOwners(mut buf[..], mut buf2[..], sys.heap.Alloc())))
}
`
	for _, flags := range [][]string{nil, {"--release"}} {
		if out := collExec(t, memNewBuild(t, src, flags...)); out != "true\n" {
			t.Errorf("%v: same owners: %q", flags, out)
		}
	}
}

// memNewPlantBlocks are written into the copy of std/mem beside the new
// allocators' test files. The first three leave a Box live through a
// Limit, a Failing and a Fallback over sys.heap: the test heap's own leak
// check must see each (exit 102), so the three pass their requests on to
// the heap they wrap. The fourth changes one word of a FixedHeap's buffer
// behind its back: ThWalk must say so (the Assert fails, exit 101), so the
// clean blocks' walks mean something.
const memNewPlantBlocks = `test "plant: the test heap sees a leak through Limit" (sys: &System) {
    l := Limit.New(sys.heap.Alloc(), 1_000)
    b := try Box[int].New(l.Alloc(), 1)
    unsafe "a planted leak" {
        raw.Forget(b)
    }
}

test "plant: the test heap sees a leak through Failing" (sys: &System) {
    f := Failing.New(sys.heap.Alloc(), -1)
    b := try Box[int].New(f.Alloc(), 1)
    unsafe "a planted leak" {
        raw.Forget(b)
    }
}

test "plant: the test heap sees a leak through Fallback" (sys: &System) {
    var empty: [1]u8 = [0; 1]
    k := Fallback.New(sys.heap.Alloc(), mut empty[0..0])
    b := try Box[int].New(k.Alloc(), 1)
    unsafe "a planted leak" {
        raw.Forget(b)
    }
}

test "plant: ThWalk sees a header changed behind the heap's back" {
    var buf: [4104]u8 = [0; 4104]
    lead := ThLead(buf[..])
    h := FixedHeap.New(mut buf[lead..lead + 4096])
    p := core.AllocBytes(h.Alloc(), 64, 8)
    q := core.AllocBytes(h.Alloc(), 64, 8)
    Assert(!raw.IsNull(p) && !raw.IsNull(q) && ThWalk(&h) == 0)
    unsafe "the planted damage: the prev word of q's header, 8 bytes below q" {
        raw.Write[u32](raw.PtrCast[u8, u32](raw.Offset(q, -8)), 3)
    }
    Assert(ThWalk(&h) == 0)
}
`

// TestSTDMEM_NewAllocTestBlocks: mk test --std=std.mem passes every block
// of std/mem/tests_fixedheap.mk and tests_wrappers.mk, dev and release,
// and the planted blocks fail with exit 102 (a leak) and 101 (the walk).
func TestSTDMEM_NewAllocTestBlocks(t *testing.T) {
	t.Parallel()
	var names []string
	for _, f := range []string{"tests_fixedheap.mk", "tests_wrappers.mk"} {
		src, err := os.ReadFile(filepath.Join("mem", f))
		if err != nil {
			t.Fatal(err)
		}
		names = append(names, testNames(string(src))...)
	}
	if len(names) < 35 {
		t.Fatalf("the new allocators have %d test blocks, want at least 35", len(names))
	}
	plants := map[string]string{
		"plant: the test heap sees a leak through Limit":             "exit 102",
		"plant: the test heap sees a leak through Failing":           "exit 102",
		"plant: the test heap sees a leak through Fallback":          "exit 102",
		"plant: ThWalk sees a header changed behind the heap's back": "exit 101",
	}
	for _, flags := range [][]string{nil, {"--release"}} {
		root := t.TempDir()
		plant := "import std.core\nimport std.raw\n\n" + memNewPlantBlocks
		stdDir := memNewCopyStd(t, root, map[string]string{"mem/tests_zz_newplant.mk": plant})
		out, _ := mkCmd(t, root, stdDir, append([]string{"test", "--std=std.mem"}, flags...)...)
		if strings.Contains(out, "no usable LLVM") {
			t.Skipf("needs the LLVM toolchain: %s", out)
		}
		res := parseStdTest(out, "std.mem")
		for _, n := range names {
			if r, ok := res[n]; !ok || !r.pass {
				t.Errorf("%v: block %q: %+v\n%s", flags, n, r, out)
			}
		}
		for name, reason := range plants {
			if r := res[name]; r.pass || !strings.Contains(r.reason, reason) {
				t.Errorf("%v: planted block %q: want a failure with %s, have %+v\n%s", flags, name, reason, r, out)
			}
		}
	}
}

// memBlockPlants are planted bugs that only a test block can see, each with
// the block that must fail under it: the tapes of the differential tests
// run over buffers and inner allocators where these bugs change no line.
var memBlockPlants = []struct {
	plant memPlant
	block string
}{
	{memPlant{"shape-keeps-a-level-no-block-needs", "mem/fixedheap.mk",
		"        if n > span {\n            best = fls",
		"        if n >= span {\n            best = fls"},
		"FixedHeap: every buffer of 96 bytes or more holds a heap, and a longer one never a smaller block"},
	{memPlant{"shape-counts-blocks-its-lists-cannot-hold", "mem/fixedheap.mk",
		"        var n := (8 << fls) - 1\n",
		"        var n := (8 << fls) - 1 + room\n"},
		"FixedHeap: every buffer of 96 bytes or more holds a heap, and a longer one never a smaller block"},
	{memPlant{"fit-serves-less-than-promised", "mem/fixedheap.mk",
		"    if g != 0 || need < 32 {\n        return g\n    }",
		"    if g != 0 || need < 34 {\n        return g\n    }"},
		"FixedHeap: the fit a request is promised, at 248 bytes and at 256"},
	{memPlant{"fallback-asks-inner-for-zero-bytes", "mem/fallback.mk",
		"    if size == 0 {\n        return 1\n    }\n    return size",
		"    if size == 0 {\n        return 0\n    }\n    return size"},
		"Fallback: a zero-byte block is one byte of the other allocator, so it is never taken for a block of the buffer"},
}

// TestSTDMEM_NewAllocBlockPlantsAreSeen: each planted bug, built into a
// copy of std, fails the test block named beside it, which passes over the
// unchanged std (TestSTDMEM_NewAllocTestBlocks).
func TestSTDMEM_NewAllocBlockPlantsAreSeen(t *testing.T) {
	t.Parallel()
	for _, c := range memBlockPlants {
		t.Run(c.plant.name, func(t *testing.T) {
			t.Parallel()
			root := t.TempDir()
			stdDir := memNewCopyStd(t, root, map[string]string{c.plant.file: memPlantSource(t, c.plant)})
			out, _ := mkCmd(t, root, stdDir, "test", "--std=std.mem", "-run", c.block)
			if strings.Contains(out, "no usable LLVM") {
				t.Skipf("needs the LLVM toolchain: %s", out)
			}
			r, ok := parseStdTest(out, "std.mem")[c.block]
			if !ok {
				t.Fatalf("plant %s: block %q did not run:\n%s", c.plant.name, c.block, out)
			}
			if r.pass {
				t.Errorf("plant %s: block %q passes", c.plant.name, c.block)
			}
		})
	}
}

// memNewEvalStats runs one list's growth through a Limit and a Failing
// over a's allocator and packs what they counted in one int.
const memNewEvalStats = `import std.mem

Stats(a: &Arena): int {
    l := mem.Limit.New(a.Alloc(), 200)
    f := mem.Failing.New(l.Alloc(), 3)
    var xs := HeapList[int].New(f.Alloc())
    var held := 0
    for i in 0..100 {
        xs.Push(f.Alloc(), i) else {
            break
        }
        held += 1
    }
    mid := l.Bytes() * 1000 + l.Left()
    xs.Free(f.Alloc())
    return ((mid * 100 + held) * 100 + f.Requests()) * 10 + f.Failed() + l.Bytes()
}

const S = Stats(EvalArena())

export Main(sys: &System): WriteError!void {
    var out := sys.Stdout()
    r := Stats(sys.arena)
    try Print(mut out, "{same}\n", (same: S == r && S > 0))
}
`

// TestSTDMEM_LimitAndFailingAtCompileTime: a Limit and a Failing over
// EvalArena() evaluate in a const, as a Counting does, and count exactly
// what the same function counts natively over sys.arena.
func TestSTDMEM_LimitAndFailingAtCompileTime(t *testing.T) {
	t.Parallel()
	for _, flags := range [][]string{nil, {"--release"}} {
		if out := collExec(t, memNewBuild(t, memNewEvalStats, flags...)); out != "true\n" {
			t.Errorf("%v: got %q, want the const and the native call to agree", flags, out)
		}
	}
}

// TestSTDMEM_BufferAllocatorsRefusedAtCompileTime: a FixedHeap and a
// Fallback in a const's evaluation are E0901 with the pointer-bytes
// refusal, as a Fixed is: each reads its buffer's address.
func TestSTDMEM_BufferAllocatorsRefusedAtCompileTime(t *testing.T) {
	t.Parallel()
	for _, c := range []struct{ name, make, file string }{
		{"FixedHeap", "var f := mem.FixedHeap.New(mut buf[..])", "std/mem/fixedheap.mk"},
		{"Fallback", "var f := mem.Fallback.New(a.Alloc(), mut buf[..])", "std/mem/"},
	} {
		src := `import std.mem

Use(a: &Arena): int {
    var buf: [256]u8 = [0; 256]
    ` + c.make + `
    f.Reset()
    return 1
}

const F = Use(EvalArena())

export Main(sys: &System): WriteError!void {
    var out := sys.Stdout()
    try Print(mut out, "{F}\n", (F))
}
`
		out, status := memCheck(t, src)
		if status == 0 || !strings.Contains(out, "E0901") || !strings.Contains(out, "pointer-bytes") || !strings.Contains(out, c.file) {
			t.Errorf("%s: want E0901 pointer-bytes traced into %s, got exit %d:\n%s", c.name, c.file, status, out)
		}
	}
}
