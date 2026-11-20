// Why: Arena.NewIn(a: &Alloc) makes an arena whose chunks come from a, which
// opened soundness holes around Send, sim.Sim and proc.Run.
// What: TestWitnesses, TestNewInLoans and
// TestBudgetReachesArenaAPIs.
// How: each tests/soundness/witness/D827-*.mk is judged by its verdict line:
// its `// <- Exxxx` markers, or its last output line.

package std

import (
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"
)

var (
	// A marker names one code or several, `// <- E0505 E0604`, the corpus
	// form that TestFlowsWitnesses reads (internal/corpus parseMarker).
	dfPack05Marker = regexp.MustCompile(`// <- ((?:E\d{4}[ \t]*)+)`)
	dfPack05Diag   = regexp.MustCompile(`(?m)^main\.mk:(\d+):\d+: (E\d{4}) `)
)

// TestWitnesses judges tests/soundness/witness/D827-*.mk. The
// run witnesses, pr1 and pr1e at 20 rounds, are a smoke check that the
// program runs correctly: the race they were written for was rare even
// with the hole open (6 mixed in 1,000 rounds, 0 in the first 300), so 20
// rounds cannot tell a regressed tree. The mechanical guard is the E1001
// (an Arena is not Send) at run.mk's s.go should a reader take a
// `mut Arena` again.
//
// The witnesses cover the Send hole (p1, p2), the Sim hole (s1, s2),
// proc.Run's (pr1, pr1e), a Sim in a HeapList, an optional, a Box, a
// generic struct and a tuple (sl1 to sl3, sl7, sl8), a Sim swapped or
// replaced into an outer frame (sl4, sl5), a Sim sent on a channel (ch1)
// and an arena as a spawned receiver (gs1). std.mem's tests_arena.mk holds
// the allocator counts.
func TestWitnesses(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("..", "tests", "soundness", "witness", "D827-*.mk"))
	if err != nil {
		t.Fatal(err)
	}
	if len(files) != 16 {
		t.Fatalf("want the 16 witnesses D827-*.mk, found %d: %v", len(files), files)
	}
	for _, f := range files {
		b, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		text := strings.ReplaceAll(string(b), "\r\n", "\n")
		lines := strings.Split(text, "\n")
		t.Run(filepath.Base(f), func(t *testing.T) {
			verdict := strings.TrimPrefix(lines[0], "// verdict: ")
			switch {
			case strings.HasPrefix(verdict, "reject "):
				var want []string
				for i, l := range lines {
					for _, m := range dfPack05Marker.FindAllStringSubmatch(l, -1) {
						for _, c := range strings.Fields(m[1]) {
							want = append(want, strconv.Itoa(i+1)+" "+c)
						}
					}
				}
				out, status := dfRun(t, map[string]string{"main.mk": text}, "check", "main.mk")
				var got []string
				for _, m := range dfPack05Diag.FindAllStringSubmatch(out, -1) {
					got = append(got, m[1]+" "+m[2])
				}
				slices.Sort(want)
				slices.Sort(got)
				var codes []string
				for _, w := range want {
					codes = append(codes, strings.Fields(w)[1])
				}
				if status == 0 || !slices.Equal(got, want) || len(want) == 0 {
					t.Fatalf("mk check: exit %d, diagnostics %v, want %v (the markers)\n%s", status, got, want, out)
				}
				for _, c := range strings.Fields(strings.TrimPrefix(verdict, "reject ")) {
					if !slices.Contains(codes, c) {
						t.Fatalf("the verdict names %s, which no marker does", c)
					}
				}
			case strings.HasPrefix(verdict, "run "):
				want := strings.TrimPrefix(lines[1], "// want: ")
				args := append([]string{"run", "main.mk", "--"}, strings.Fields(strings.TrimPrefix(verdict, "run "))...)
				out, status := dfRun(t, map[string]string{"main.mk": text}, args...)
				if status != 0 || !strings.HasSuffix(strings.TrimRight(out, "\n"), want) {
					t.Fatalf("mk %s: exit %d, want exit 0 and output ending in %q\n%s", strings.Join(args, " "), status, want, out)
				}
			default:
				t.Fatalf("no verdict line: %q", lines[0])
			}
		})
	}
}

// TestNewInLoans: an arena from NewIn holds its source's loan,
// a Sub the arena's, so neither outlives, nor survives a reset, free or
// move of, the allocator behind it; an arena over another arena's Alloc
// holds that arena's loan; and no NewIn arena reaches another task through
// a Box, a Mutex or a Chan. Each is the one diagnostic named.
func TestNewInLoans(t *testing.T) {
	dfPack05Check(t, []dfPack05Case{
		{"the arena leaves the Fixed's frame", `import std.mem

Make(sys: &System): OutOfMemory!Arena {
    var buf: [8192]u8 = [0; 8192]
    fixed := mem.Fixed.New(mut buf[..])
    return try Arena.NewIn(fixed.Alloc())
}

export Main(sys: &System) {
    var a := Make(sys) else {
        return
    }
    a.Free()
}
`, "main.mk:6:5: E0603"},
		{"a Sub of a Sub outlives its parent", `import std.mem

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    var b := a.Sub() else {
        a.Free()
        return
    }
    var c := b.Sub() else {
        b.Free()
        a.Free()
        return
    }
    b.Free()
    c.Free()
    a.Free()
}
`, "main.mk:17:5: E0503"},
		{"the Fixed reset under the arena", `import std.mem

export Main(sys: &System) {
    buf := sys.arena.Slice[u8](65536) else {
        return
    }
    var fixed := mem.Fixed.New(buf)
    var a := Arena.NewIn(fixed.Alloc()) else {
        return
    }
    fixed.Reset()
    a.Free()
}
`, "main.mk:11:5: E0501"},
		{"the Fixed reset under a reset arena", `import std.mem

export Main(sys: &System) {
    buf := sys.arena.Slice[u8](65536) else {
        return
    }
    var fixed := mem.Fixed.New(buf)
    var a := Arena.NewIn(fixed.Alloc()) else {
        return
    }
    a.Reset()
    fixed.Reset()
    a.Free()
}
`, "main.mk:12:5: E0501"},
		{"a reset arena leaves the Fixed's frame", `import std.mem

Make(sys: &System): OutOfMemory!Arena {
    var buf: [8192]u8 = [0; 8192]
    fixed := mem.Fixed.New(mut buf[..])
    var a := try Arena.NewIn(fixed.Alloc())
    a.Reset()
    return a
}

export Main(sys: &System) {
    var a := Make(sys) else {
        return
    }
    a.Free()
}
`, "main.mk:8:5: E0603"},
		{"the parent freed under a reset Sub", `import std.mem

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    var s := a.Sub() else {
        a.Free()
        return
    }
    s.Reset()
    a.Free()
    s.Free()
    _ = counting.Live()
}
`, "main.mk:13:5: E0503"},
		{"the Fixed moved under the arena", `import std.mem

export Main(sys: &System) {
    buf := sys.arena.Slice[u8](65536) else {
        return
    }
    fixed := mem.Fixed.New(buf)
    var a := Arena.NewIn(fixed.Alloc()) else {
        return
    }
    moved := fixed
    a.Free()
    _ = moved.Alloc()
}
`, "main.mk:11:5: E0503"},
		{"the parent freed under its Sub", `import std.mem

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    var s := a.Sub() else {
        a.Free()
        return
    }
    a.Free()
    s.Free()
    _ = counting.Live()
}
`, "main.mk:12:5: E0503"},
		{"the Counting moved under the arena", `import std.mem

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    moved := counting
    a.Free()
    _ = moved.Live()
}
`, "main.mk:8:5: E0503"},
		{"the parent moved and freed under its Sub", `import std.mem

export Main(sys: &System) {
    buf := sys.arena.Slice[u8](65536) else {
        return
    }
    var fixed := mem.Fixed.New(buf)
    var a := Arena.NewIn(fixed.Alloc()) else {
        return
    }
    var sub := a.Sub() else {
        a.Free()
        return
    }
    b := a
    b.Free()
    sub.Free()
}
`, "main.mk:15:5: E0503"},
		{"a str of a Sub read after the Fixed is reset", `import std.mem

export Main(sys: &System) {
    buf := sys.arena.Slice[u8](65536) else {
        return
    }
    var fixed := mem.Fixed.New(buf)
    var a := Arena.NewIn(fixed.Alloc()) else {
        return
    }
    var sub := a.Sub() else {
        a.Free()
        return
    }
    s := sub.Dup("kept") else {
        sub.Free()
        a.Free()
        return
    }
    sub.Free()
    a.Free()
    fixed.Reset()
    sys.Print("{s}\n", (s)) else {
    }
}
`, "main.mk:20:5: E0503"},
		{"a Sim over a NewIn arena moved into a task", `import std.mem
import std.sim

Work(s: sim.Sim) {
    s.Free()
}

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var arena := Arena.NewIn(counting.Alloc()) else {
        return
    }
    s := sim.Sim.New(&arena, 7) else {
        arena.Free()
        return
    }
    scope sc := sys.io.Scope() {
        sc.go Work(s)
    }
    arena.Free()
}
`, "main.mk:18:20: E1001"},
		{"an arena over another arena's Alloc, the outer one reset", `export Main(sys: &System) {
    var outer := Arena.New(sys.heap) else {
        return
    }
    var inner := Arena.NewIn(outer.Alloc()) else {
        outer.Free()
        return
    }
    outer.Reset()
    inner.Free()
    outer.Free()
}
`, "main.mk:9:5: E0501"},
		{"an arena over another arena's Alloc, the outer one freed", `export Main(sys: &System) {
    var outer := Arena.New(sys.heap) else {
        return
    }
    var inner := Arena.NewIn(outer.Alloc()) else {
        outer.Free()
        return
    }
    outer.Free()
    inner.Free()
}
`, "main.mk:9:5: E0503"},
		{"an arena over a temporary Counting", `import std.mem

export Main(sys: &System) {
    var a := Arena.NewIn(mem.Counting.New(sys.heap.Alloc()).Alloc()) else {
        return
    }
    a.Free()
}
`, "E0506"},
		{"a NewIn arena in a Box moved to a task", `import std.mem

Work(h: &Heap, b: Box[Arena]) {
    a := b.Take(h.Alloc())
    a.Free()
}

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    b := Box[Arena].New(sys.heap.Alloc(), a) else {
        return
    }
    scope s := sys.io.Scope() {
        s.go Work(sys.heap, b)
    }
}
`, "E1001"},
		{"a NewIn arena in a Mutex shared with a task", `import std.mem

Work(m: &Mutex[?Arena]) {
}

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    var m := Mutex[?Arena].New(some(a))
    scope s := sys.io.Scope() {
        s.go Work(&m)
    }
    if x := m.Into() {
        x.Free()
    }
}
`, "E1002"},
		{"a Chan of arenas shared with a task", `Work(c: &Chan[Arena]) {
}

export Main(sys: &System) {
    var ch := Chan[Arena].New(sys.heap.Alloc(), 1) else {
        return
    }
    scope s := sys.io.Scope() {
        s.go Work(&ch)
    }
    ch.FreeEmpty(sys.heap.Alloc())
}
`, "E1002"},
		{"control: arenas over a Counting and an arena's Alloc, freed in order", `import std.mem

export Main(sys: &System) {
    counting := mem.Counting.New(sys.heap.Alloc())
    var a := Arena.NewIn(counting.Alloc()) else {
        return
    }
    var s := a.Sub() else {
        a.Free()
        return
    }
    var inner := Arena.NewIn(s.Alloc()) else {
        s.Free()
        a.Free()
        return
    }
    inner.Free()
    s.Free()
    a.Free()
    _ = counting.Live()
}
`, ""},
	})
	t.Run("a Sub of a Sub leaves the Fixed's frame", func(t *testing.T) {
		out, status := dfRun(t, map[string]string{"main.mk": `import std.mem

Make(sys: &System): OutOfMemory!Arena {
    buf := try sys.arena.Slice[u8](65536)
    fixed := mem.Fixed.New(buf)
    var a := try Arena.NewIn(fixed.Alloc())
    defer a.Free()
    var b := try a.Sub()
    defer b.Free()
    c := try b.Sub()
    return c
}

export Main(sys: &System) {
    var c := Make(sys) else {
        return
    }
    c.Free()
}
`}, "check", "main.mk")
		if status == 0 || !strings.Contains(out, "main.mk:11:5: E0603 ") || !strings.Contains(out, "main.mk:9:11: E0503 ") || strings.Count(out, ": E") != 2 {
			t.Fatalf("mk check: exit %d, want E0603 at the return and E0503 at b's deferred Free\n%s", status, out)
		}
	})
	t.Run("a List in an arena over a Fixed leaves the Fixed's frame in a struct", func(t *testing.T) {
		out, status := dfRun(t, map[string]string{"main.mk": `import std.mem

struct Job {
    xs: List[int]
    n: int
}

Make(sys: &System): OutOfMemory!Job {
    buf := try sys.arena.Slice[u8](65536)
    var fixed := mem.Fixed.New(buf)
    var inner := try Arena.NewIn(fixed.Alloc())
    var xs := List[int].New(&inner)
    xs.Push(1) else {
    }
    j := Job(xs: xs, n: 1)
    inner.Free()
    return j
}

export Main(sys: &System) {
    j := Make(sys) else {
        return
    }
    _ = j.xs.Len()
}
`}, "check", "main.mk")
		if status == 0 || !strings.Contains(out, "main.mk:16:5: E0503 ") || !strings.Contains(out, "main.mk:17:5: E0603 ") || strings.Count(out, ": E") != 2 {
			t.Fatalf("mk check: exit %d, want E0503 at inner's Free and E0603 at the return\n%s", status, out)
		}
	})
}

// TestBudgetReachesArenaAPIs: DF-pack-05's program over
// NewIn, and fs.ReadBytes, sim.Sim.New and proc.Run over an arena whose
// source is a Counting over a Fixed: a budget too small fails cleanly with
// OutOfMemory, a large one serves the call, and every byte is back once
// the arena is freed.
func TestBudgetReachesArenaAPIs(t *testing.T) {
	t.Run("compress.Deflate", func(t *testing.T) {
		dfWant(t, map[string]string{"main.mk": `import std.compress
import std.mem

Deflate(c: &mem.Counting, data: []u8): OutOfMemory!int {
    var arena := try Arena.NewIn(c.Alloc())
    defer arena.Free()
    out := try compress.Deflate(&arena, data)
    return out.Len()
}

export Main(sys: &System): OutOfMemory|WriteError!void {
    buf := try sys.arena.Slice[u8](8388608)
    small := mem.Fixed.New(mut buf[..262144])
    cs := mem.Counting.New(small.Alloc())
    _ = Deflate(&cs, b"budgeted") else e {
        try sys.Print("small: {e}, live {l}\n", (e, l: cs.Live()))
    }
    large := mem.Fixed.New(mut buf[262144..])
    cl := mem.Counting.New(large.Alloc())
    n := try Deflate(&cl, b"budgeted")
    try sys.Print("large: {n} bytes, peak over 256 KiB {p}, live {l} bytes {b}\n", (n, p: cl.Peak() > 262144, l: cl.Live(), b: cl.Bytes()))
}
`}, "small: OutOfMemory, live 0\nlarge: 10 bytes, peak over 256 KiB true, live 0 bytes 0\n")
	})
	t.Run("fs.ReadBytes", func(t *testing.T) {
		dfWant(t, map[string]string{"big.txt": strings.Repeat("0123456789abcdef", 4096), "main.mk": `import std.fs
import std.mem

Read(c: &mem.Counting, io: Io): fs.Error|OutOfMemory!int {
    var arena := try Arena.NewIn(c.Alloc())
    defer arena.Free()
    b := try fs.ReadBytes(&arena, io, "big.txt")
    return b.Len()
}

export Main(sys: &System): fs.Error|OutOfMemory|WriteError!void {
    buf := try sys.arena.Slice[u8](1048576)
    small := mem.Fixed.New(mut buf[..32768])
    cs := mem.Counting.New(small.Alloc())
    _ = Read(&cs, sys.io) else e {
        try sys.Print("small: {e}, live {l}\n", (e, l: cs.Live()))
    }
    large := mem.Fixed.New(mut buf[32768..])
    cl := mem.Counting.New(large.Alloc())
    n := try Read(&cl, sys.io)
    try sys.Print("large: {n} bytes, live {l}\n", (n, l: cl.Live()))
}
`}, "small: OutOfMemory, live 0\nlarge: 65536 bytes, live 0\n")
	})
	t.Run("sim.Sim.New", func(t *testing.T) {
		dfWant(t, map[string]string{"main.mk": `import std.mem
import std.sim

Run(c: &mem.Counting): OutOfMemory!int {
    var arena := try Arena.NewIn(c.Alloc())
    defer arena.Free()
    var s := try sim.Sim.New(&arena, 7)
    defer s.Free()
    _ = try s.Arena().Dup("the world's bytes")
    _ = try s.Arena().Slice[u8](100000)
    return c.Live()
}

export Main(sys: &System): OutOfMemory|WriteError!void {
    buf := try sys.arena.Slice[u8](1048576)
    f := mem.Fixed.New(buf)
    c := mem.Counting.New(f.Alloc())
    held := try Run(&c)
    try sys.Print("the Sim's chunks counted {k}, live {l}\n", (k: held >= 3, l: c.Live()))
}
`}, "the Sim's chunks counted true, live 0\n")
	})
	// proc.Run's two reader segments are on the process heap, so
	// the budget bounds the result Run copies into the arena: 300 KiB of
	// output does not fit in 64 KiB and does in 4 MiB.
	t.Run("proc.Run", func(t *testing.T) {
		dfWant(t, map[string]string{"main.mk": `import std.mem
import std.proc

Run(c: &mem.Counting, sys: &System, args: []str): proc.Error!(o: int, e: int, live: int) {
    var arena := try Arena.NewIn(c.Alloc())
    defer arena.Free()
    r := try proc.Run(&arena, sys.io, args, b"", 16777216)
    var bad := 0
    for b in r.stdout {
        if b != b'O' && b != b'\n' {
            bad += 1
        }
    }
    for b in r.stderr {
        if b != b'E' && b != b'\n' {
            bad += 1
        }
    }
    Assert(bad == 0 && r.code == 0)
    return (o: r.stdout.Len(), e: r.stderr.Len(), live: c.Live())
}

export Main(sys: &System): proc.Error|WriteError!void {
    if sys.args.Len() > 1 {
        var out := sys.Stdout()
        var err := sys.Stderr()
        for _ in 0..3200 {
            try out.Str("OOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO\n")
        }
        for _ in 0..1600 {
            try err.Str("EEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE\n")
        }
        return
    }
    args := [sys.args[0], "child"]
    buf := try sys.arena.Slice[u8](4194304)
    small := mem.Fixed.New(mut buf[..65536])
    cs := mem.Counting.New(small.Alloc())
    _ = Run(&cs, sys, args[..]) else e {
        try sys.Print("small: {e}, live {l}\n", (e, l: cs.Live()))
    }
    large := mem.Fixed.New(mut buf[65536..])
    cl := mem.Counting.New(large.Alloc())
    got := try Run(&cl, sys, args[..])
    try sys.Print("large: {o} and {e} bytes, peak over 300 KiB {p}, live {l} then {k}\n", (o: got.o, e: got.e, p: cl.Peak() > 307200, l: got.live > 0, k: cl.Live()))
}
`}, "small: OutOfMemory, live 0\nlarge: 204800 and 102400 bytes, peak over 300 KiB true, live true then 0\n")
	})
}
