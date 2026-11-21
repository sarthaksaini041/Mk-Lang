// Why: `ends` lets a callee end loans on its argument, and the exemptions
// around it are where unsound programs could slip through.
// What: tests of `ends` at calls that also store, on error edges, through
// every callee kind and through argument slots, of provenance kept across
// `ends` on views and allocators, and of Result.Reads for E0402's facts.
// How: hand-built bodies (endsStoreBody, tieValue, tieWorld), checked for
// E0505, E0501, E0503 and E1102.

package borrow

import (
	"testing"

	"mk/internal/diag"
	"mk/internal/mir"
	"mk/internal/source"
	"mk/internal/types"
)

// endsStoreBody is `struct O { r: ?&i32 }` and a caller of O.Clear(mut self,
// ...) that stores &x into o in the call itself, through `x: &i32 into self`
// (store false) or `q: &&i32` with `*q into self` (store true):
//
//	y := 1
//	var o := O(r: some(&y))      // old: o holds &y before the call
//	x := 5
//	o.Clear(&x)                  // or o.Clear(&&x)
//	<x ends>; <y ends>; Use(&o)
//
// With fallible, Clear fails with an error and the error block does the same
// ends and use. It returns the spans of &x and &y.
func endsStoreBody(t *testing.T, store, ends, old, fallible bool) (*mb, mir.SpanID, mir.SpanID) {
	k := newKit(t)
	ri := refI32(k)
	ort := k.tab.Optional(ri)
	k.structItem(k.main, "O", 0, false, false, field("r", ort))
	ot := k.named("O")
	errs := types.EmptyErrors
	if fallible {
		errs = k.errs("Failed")
	}
	var clr *types.Signature
	if store {
		clr = k.method("O", "Clear", types.ByMut, ot, []types.Param{k.param("q", k.tab.Ref(ri))}, types.Void, errs)
		clr.Flows.Stores = []types.Store{{From: 2, Into: 1}}
	} else {
		clr = k.method("O", "Clear", types.ByMut, ot, []types.Param{{Name: k.in.Intern("x"), Type: ri, Into: 1}}, types.Void, errs)
	}
	if ends {
		clr.Flows.Ends = []types.ParamIndex{1}
	}
	m := k.body(k.sig("F", nil, types.Void, types.EmptyErrors))
	y := m.user("y", types.I32, false)
	m.set(y, use(imm(types.I32, 1)))
	o := m.user("o", ot, true)
	r := m.temp(ort)
	var ySite mir.SpanID
	if old {
		ty := m.temp(ri)
		ySite = m.set(ty, ref(m.local(y)))
		m.set(r, m.agg(mir.AggSome, types.NoItem, ort, cp(m.local(ty))))
		m.set(o, m.agg(mir.AggStruct, k.item("O"), ot, cp(m.local(r))))
		m.end(r, ty)
	} else {
		m.set(r, m.agg(mir.AggNone, types.NoItem, ort))
		m.set(o, m.agg(mir.AggStruct, k.item("O"), ot, cp(m.local(r))))
		m.end(r)
	}
	x := m.user("x", types.I32, false)
	m.set(x, use(imm(types.I32, 5)))
	tx := m.temp(ri)
	xSite := m.set(tx, ref(m.local(x)))
	arg := tx
	var tq mir.LocalID
	if store {
		tq = m.temp(k.tab.Ref(ri))
		m.set(tq, ref(m.local(tx)))
		arg = tq
	}
	to := m.temp(k.tab.Mut(ot))
	m.set(to, mutRef(m.local(o)))
	d := m.temp(types.Void)
	ok := m.block()
	args := []mir.Arg{argMove(m.local(to)), argCopy(m.local(arg))}
	tail := func() {
		m.end(to)
		if store {
			m.end(tq)
		}
		m.end(tx, x, y)
		m.useRef(m.local(o), ot)
		m.end(o)
		m.ret(mir.ExitNormal)
	}
	if fallible {
		bad := m.block()
		e := m.temp(k.tab.ErrorSetType(errs))
		m.callErr(k.item("O.Clear"), nil, args, m.local(d), ok, mir.EdgeElse, bad, e)
		m.at(bad)
		m.end(e)
		tail()
	} else {
		m.call(k.item("O.Clear"), nil, args, m.local(d), ok)
	}
	m.at(ok)
	tail()
	return m, xSite, ySite
}

// TestR18_EndsKeepsLoansStoredByTheSameCall: a callee with
// `ends self` that also stores an argument into self (`x into self` or `*q
// into self`) ends what self held before the call, not what the call itself
// stored. The stored &x outlives x in o: E0505 at &x, as without `ends`.
func TestR18_EndsKeepsLoansStoredByTheSameCall(t *testing.T) {
	for _, tc := range []struct {
		name        string
		store, ends bool
	}{{"into-ends", false, true}, {"into-control", false, false}, {"store-ends", true, true}, {"store-control", true, false}} {
		t.Run(tc.name, func(t *testing.T) {
			m, xs, _ := endsStoreBody(t, tc.store, tc.ends, false, false)
			m.expect(t, m.check(t), diag.E0505, xs)
		})
	}
}

// TestR18_EndsStillEndsOldLoans: the same call does end what o held before
// it: the loan on y that o held before Clear is gone on the success
// edge, so y may end; without `ends` it is E0505 at &y too.
func TestR18_EndsStillEndsOldLoans(t *testing.T) {
	for _, store := range []bool{false, true} {
		m, xs, ys := endsStoreBody(t, store, true, true, false)
		m.expect(t, m.check(t), diag.E0505, xs)
		m, xs, ys = endsStoreBody(t, store, false, true, false)
		m.expect(t, m.check(t), diag.E0505, xs, diag.E0505, ys)
	}
}

// TestR18_EndsErrorEdgeKeepsOldLoans: on the error edge of a fallible `ends`
// call nothing is ended, so the old loan on y and the stored loan on x
// are both still in o there: E0505 at &y (error path) and at &x (both).
func TestR18_EndsErrorEdgeKeepsOldLoans(t *testing.T) {
	for _, store := range []bool{false, true} {
		m, xs, ys := endsStoreBody(t, store, true, true, true)
		m.expect(t, m.check(t), diag.E0505, xs, diag.E0505, ys)
	}
}

// tieValue builds `var t := Tie(a: Cell.New(none)); t.a.Store(some(&t))`,
// the `Tie` value holding a loan on itself, and returns t.
func tieValue(k *kit, m *mb, tieT, ort, cellT types.TypeID) mir.LocalID {
	tv := m.user("t", tieT, true)
	none := m.temp(ort)
	c := m.temp(cellT)
	m.set(none, m.agg(mir.AggNone, types.NoItem, ort))
	nx := m.block()
	m.call(k.item("Cell.New"), []types.TypeID{ort}, []mir.Arg{argCopy(m.local(none))}, m.local(c), nx)
	m.at(nx)
	m.set(tv, m.agg(mir.AggStruct, k.item("Tie"), tieT, mv(m.local(c))))
	m.end(c, none)
	rt := m.temp(k.tab.Ref(tieT))
	sm := m.temp(ort)
	ra := m.temp(k.tab.Ref(cellT))
	m.set(rt, ref(m.local(tv)))
	m.set(sm, m.agg(mir.AggSome, types.NoItem, ort, cp(m.local(rt))))
	m.set(ra, ref(m.pl(tv, fld(0, cellT))))
	m.callv("Cell.Store", []types.TypeID{ort}, argCopy(m.local(ra)), argCopy(m.local(sm)))
	m.end(ra, sm, rt)
	return tv
}

// tieWorld is the fixture world with `struct Tie { a: Cell[?&Tie] }`.
func tieWorld(t *testing.T) (*kit, types.TypeID, types.TypeID, types.TypeID) {
	k := newKit(t)
	k.lib()
	k.cellNew()
	tie := k.items.AddItem(&types.Item{Module: k.main.ID, Name: k.in.Intern("Tie"), Kind: types.KindStruct,
		Key: types.ItemKey("main", "Tie")})
	k.byNm["Tie"] = tie
	tieT := k.tab.Named(tie, nil)
	ort := k.tab.Optional(k.tab.Ref(tieT))
	cellT := k.tab.Named(k.known.Cell, []types.GenericArg{types.TypeArg(ort)})
	k.items.Get(tie).Decl = &types.StructDecl{Fields: []types.FieldDecl{{Name: k.in.Intern("a"), Type: cellT}}}
	return k, tieT, ort, cellT
}

// TestR18_EndsExemptionEveryCalleeKind: `tr = mut t; Reset(move tr); Use(&t)`
// on a self-tied t is accepted (a loan on self whose every live holder is self
// does not conflict) whether Reset is a method (`Tie.Reset(mut self) ends
// self`), a fn value (`reset: fn(mut Tie) ends 1`) or an interface method
// (`Resettable.Reset(mut self) ends self`): each call clears H(t) on success,
// so each formation gets the exemption. The twin with a second live holder of
// the self-loan (`keep := &t` used after the call) is E0501 at `mut t` through
// each kind.
func TestR18_EndsExemptionEveryCalleeKind(t *testing.T) {
	for _, kind := range []mir.CalleeKind{mir.CallDirect, mir.CallValue, mir.CallInterface} {
		for _, other := range []bool{false, true} {
			k, tieT, ort, cellT := tieWorld(t)
			reset := k.method("Tie", "Reset", types.ByMut, tieT, nil, types.Void, types.EmptyErrors)
			reset.Flows.Ends = []types.ParamIndex{1}
			ft := k.tab.Fn(types.FnType{Params: []types.FnParam{{Type: k.tab.Mut(tieT)}}, Result: types.Void,
				Errors: types.EmptyErrors, Ends: []types.ParamIndex{1}})
			rs := k.items.AddItem(&types.Item{Module: k.main.ID, Name: k.in.Intern("Resettable"), Kind: types.KindInterface,
				Key: types.ItemKey("main", "Resettable"), Decl: &types.InterfaceDecl{}})
			im := types.Signature{Name: k.in.Intern("Reset"), Receiver: types.ByMut, Result: types.Void, Errors: types.EmptyErrors,
				Params: []types.Param{{Name: source.SymSelf, Type: k.tab.Mut(k.tab.SelfType())}}}
			im.Flows.Ends = []types.ParamIndex{1}
			s := k.sig("F", []types.Param{k.param("reset", ft)}, types.Void, types.EmptyErrors)
			m := k.body(s)
			tv := tieValue(k, m, tieT, ort, cellT)
			var keep mir.LocalID
			if other {
				keep = m.user("keep", k.tab.Ref(tieT), false)
				m.set(keep, ref(m.local(tv)))
			}
			tr := m.temp(k.tab.Mut(tieT))
			form := m.set(tr, mutRef(m.local(tv)))
			d := m.temp(types.Void)
			n2 := m.block()
			args := m.b.AddArgs(argMove(m.local(tr)))
			switch kind {
			case mir.CallDirect:
				m.term(mir.Terminator{Kind: mir.TermCall, Callee: mir.Callee{Kind: mir.CallDirect, Fn: mir.FnRef{Item: reset.Item}},
					Args: args, Dest: m.local(d), Target: n2, Spawn: mir.NoLocal})
			case mir.CallValue:
				m.term(mir.Terminator{Kind: mir.TermCall, Callee: mir.Callee{Kind: mir.CallValue, Value: cp(m.local(1))},
					Args: args, Dest: m.local(d), Target: n2, Spawn: mir.NoLocal})
			case mir.CallInterface:
				m.term(mir.Terminator{Kind: mir.TermCall, Callee: mir.Callee{Kind: mir.CallInterface, Iface: rs, Method: 0, SelfType: tieT},
					Args: args, Dest: m.local(d), Target: n2, Spawn: mir.NoLocal})
			}
			m.at(n2)
			m.end(tr)
			if other {
				m.callv("Use", []types.TypeID{tieT}, argCopy(m.local(keep)))
				m.end(keep)
			} else {
				m.useRef(m.local(tv), tieT)
			}
			m.end(tv)
			m.ret(mir.ExitNormal)
			env := k.env(s)
			env.Method = func(it types.ItemID, i uint32) *types.Signature {
				if it == rs && i == 0 {
					return &im
				}
				return nil
			}
			r := Check(m.b, env)
			if other {
				m.expect(t, r, diag.E0501, form)
			} else {
				m.expect(t, r)
			}
		}
	}
}

// TestR18_EndsThroughArgSlot, at the call: `Free2(x: Tie, b:
// bool) ends x` called on a self-tied t as `Free2(t, Cond())` is accepted
// whether lower passes t directly (`c = Cond(); Free2(move t, copy c)`) or,
// because the later operand is not inert, through an argument slot (`ts =
// move t; c = Cond(); Free2(move ts, copy c)`): the slot's move of t
// is the ends argument's formation and gets the exemption. With a by-value
// `Free3(x: Tie, b: bool)` that does not end x, the slot's move is E0503.
func TestR18_EndsThroughArgSlot(t *testing.T) {
	for _, slot := range []bool{false, true} {
		for _, ends := range []bool{true, false} {
			k, tieT, ort, cellT := tieWorld(t)
			free := k.fn("Free2", []types.Param{k.param("x", tieT), k.param("b", types.Bool)}, types.Void, types.EmptyErrors)
			if ends {
				free.Flows.Ends = []types.ParamIndex{1}
			}
			m := k.body(k.sig("F", nil, types.Void, types.EmptyErrors))
			tv := tieValue(k, m, tieT, ort, cellT)
			cb := m.temp(types.Bool)
			var mov mir.SpanID
			if slot {
				ts := m.temp(tieT)
				mov = m.set(ts, use(mv(m.local(tv))))
				n3 := m.block()
				m.call(k.item("Cond"), nil, nil, m.local(cb), n3)
				m.at(n3)
				m.callv("Free2", nil, argMove(m.local(ts)), argCopy(m.local(cb)))
				m.end(ts)
			} else {
				n3 := m.block()
				m.call(k.item("Cond"), nil, nil, m.local(cb), n3)
				m.at(n3)
				mov = m.callv("Free2", nil, argMove(m.local(tv)), argCopy(m.local(cb)))
			}
			m.end(cb, tv)
			m.ret(mir.ExitNormal)
			r := m.check(t)
			if ends {
				m.expect(t, r)
			} else {
				m.expect(t, r, diag.E0503, mov)
			}
		}
	}
}

// TestWrapperThroughArgSlot, at the declaration: `W(x:
// Tie, y: Tie) ends x { Free2(x, Cond()) }` proves its ends whether x is
// passed directly or through an argument slot, so neither is E1102; passing
// y through the slot instead proves nothing and is E1102 at the signature.
func TestWrapperThroughArgSlot(t *testing.T) {
	for _, tc := range []struct {
		name      string
		slot, ofY bool
	}{{"direct", false, false}, {"slot", true, false}, {"slot-of-other", true, true}} {
		t.Run(tc.name, func(t *testing.T) {
			k, tieT, _, _ := tieWorld(t)
			free := k.fn("Free2", []types.Param{k.param("x", tieT), k.param("b", types.Bool)}, types.Void, types.EmptyErrors)
			free.Flows.Ends = []types.ParamIndex{1}
			s := k.sig("W", []types.Param{k.param("x", tieT), k.param("y", tieT)}, types.Void, types.EmptyErrors)
			s.Flows.Ends = []types.ParamIndex{1}
			s.Span = source.Span{File: kitFile, Start: 3, End: 4}
			m := k.body(s)
			src := mir.LocalID(1)
			if tc.ofY {
				src = 2
			}
			cb := m.temp(types.Bool)
			if tc.slot {
				ts := m.temp(tieT)
				m.set(ts, use(mv(m.local(src))))
				n3 := m.block()
				m.call(k.item("Cond"), nil, nil, m.local(cb), n3)
				m.at(n3)
				m.callv("Free2", nil, argMove(m.local(ts)), argCopy(m.local(cb)))
				m.end(ts)
			} else {
				n3 := m.block()
				m.call(k.item("Cond"), nil, nil, m.local(cb), n3)
				m.at(n3)
				m.callv("Free2", nil, argMove(m.local(src)), argCopy(m.local(cb)))
			}
			m.end(cb)
			if !tc.ofY {
				m.callv("Take", []types.TypeID{tieT}, argMove(m.local(2)))
			} else {
				m.callv("Take", []types.TypeID{tieT}, argMove(m.local(1)))
			}
			m.ret(mir.ExitNormal)
			r := m.check(t)
			var e1102 int
			for _, d := range r.Diags {
				if d.Code == diag.E1102 {
					e1102++
				}
			}
			if want := map[bool]int{false: 0, true: 1}[tc.ofY]; e1102 != want {
				t.Fatalf("%d E1102, want %d: %v", e1102, want, got(r))
			}
		})
	}
}

// TestReadsRecordReleaseMethods: E0402's `release` and `target` facts are read
// from Res's methods, so the body's reads hold the member namespace of Res
// (keyed `main.Res:`, the key iface reads as a type's member list) and the
// signature of every method of Res, by-value or not. A body with no E0402 does
// not scan the methods.
func TestReadsRecordReleaseMethods(t *testing.T) {
	ns := types.Read{Kind: types.ReadExports, Key: types.KeyFromString("main.Res:")}
	closeSig := types.Read{Kind: types.ReadSignature, Key: types.MemberKey("main", "Res", "Close")}
	peekSig := types.Read{Kind: types.ReadSignature, Key: types.MemberKey("main", "Res", "Peek")}
	for _, leak := range []bool{true, false} {
		k := newKit(t)
		k.method("Res", "Peek", types.ByShared, k.Res, nil, types.Void, types.EmptyErrors)
		m := k.body(k.sig("Drop", nil, types.Void, types.EmptyErrors))
		f := m.user("f", k.Res, false)
		m.acquire(f)
		if !leak {
			m.close(f)
		}
		m.end(f)
		m.ret(mir.ExitNormal)
		r := m.check(t)
		if leak && (len(r.Diags) != 1 || r.Diags[0].Code != diag.E0402) {
			t.Fatalf("want one E0402: %v", got(r))
		}
		seen := map[types.Read]bool{}
		for _, rd := range r.Reads.Sorted() {
			seen[rd] = true
		}
		reads := []types.Read{ns, closeSig, peekSig}
		if !leak {
			reads = reads[:1] // the call x.Close() reads Close's signature itself
			reads = append(reads, peekSig)
		}
		for _, rd := range reads {
			if seen[rd] != leak {
				t.Errorf("leak=%v: read %v %s recorded %v, want %v (reads %v)", leak, rd.Kind, rd.Key, seen[rd], leak, r.Reads.Sorted())
			}
		}
	}
}

// TestR18_EndsKeepsViewAndAllocatorProvenance: an `ends self` reset on an
// Arena (from Arena.NewIn or Arena.Sub) or a view allocator (Fixed.New over
// a buffer) ends what was stored into its contents (`x into self`, self-loans
// included) while keeping the provenance loan the value holds on its backing
// allocator or buffer; consuming Free(self) by value still ends everything.
func TestR18_EndsKeepsViewAndAllocatorProvenance(t *testing.T) {
	t.Run("arena-keeps-backing-ends-content", func(t *testing.T) {
		for _, tc := range []struct {
			name                     string
			reset, endBacking, moved bool
		}{
			{"reset-ends-content", true, false, false},
			{"no-reset-content-outlives", false, false, false},
			{"reset-keeps-backing", true, true, false},
			{"moved-reset-keeps-backing", true, true, true},
		} {
			t.Run(tc.name, func(t *testing.T) {
				k := newKit(t)
				ri := refI32(k)
				ra := k.tab.Ref(k.Alloc)
				newIn := k.declare("Arena.NewIn", types.MemberKey("std.core", "Arena", "NewIn"), types.NoReceiver, nil, []types.Param{k.param("a", ra)}, k.Arena, types.EmptyErrors)
				newIn.Flows.Sources = []types.Source{{Param: 1}}
				k.method("Arena", "Put", types.ByShared, k.Arena, []types.Param{{Name: k.in.Intern("x"), Type: ri, Into: 1}}, types.Void, types.EmptyErrors)
				reset := k.method("Arena", "Reset", types.ByMut, k.Arena, nil, types.Void, types.EmptyErrors)
				reset.Flows.Ends = []types.ParamIndex{1}
				free := k.method("Arena", "Free", types.ByValue, k.Arena, nil, types.Void, types.EmptyErrors)
				free.Flows.Ends = []types.ParamIndex{1}

				m := k.body(k.sig("F", nil, types.Void, types.EmptyErrors))
				src := m.user("src", k.Alloc, false)
				m.set(src, m.agg(mir.AggStruct, k.known.Alloc, k.Alloc, mir.Imm(k.tab.RawPtr(types.U8), 0)))
				rsrc := m.temp(ra)
				srcSite := m.set(rsrc, ref(m.local(src)))
				a := m.user("a", k.Arena, true)
				nx := m.block()
				m.call(newIn.Item, nil, []mir.Arg{argCopy(m.local(rsrc))}, m.local(a), nx)
				m.at(nx)
				m.end(rsrc)

				short := m.user("short", types.I32, false)
				m.set(short, use(imm(types.I32, 7)))
				rsh := m.temp(ri)
				shSite := m.set(rsh, ref(m.local(short)))
				ta := m.temp(k.tab.Ref(k.Arena))
				m.set(ta, ref(m.local(a)))
				m.callv("Arena.Put", nil, argCopy(m.local(ta)), argCopy(m.local(rsh)))
				m.end(ta, rsh)

				cur := a
				if tc.moved {
					a2 := m.user("a2", k.Arena, true)
					m.set(a2, use(mv(m.local(a))))
					cur = a2
				}
				if tc.reset {
					tr := m.temp(k.tab.Mut(k.Arena))
					m.set(tr, mutRef(m.local(cur)))
					m.callv("Arena.Reset", nil, argMove(m.local(tr)))
					m.end(tr)
				}
				m.end(short)
				if tc.endBacking {
					m.end(src)
				}
				m.callv("Arena.Free", nil, argMove(m.local(cur)))
				m.end(cur)
				if cur != a {
					m.end(a)
				}
				if !tc.endBacking {
					m.end(src)
				}
				m.ret(mir.ExitNormal)

				switch {
				case !tc.reset:
					m.expect(t, m.check(t), diag.E0505, shSite)
				case tc.endBacking:
					m.expect(t, m.check(t), diag.E0505, srcSite)
				default:
					m.expect(t, m.check(t))
				}
			})
		}
	})

	t.Run("view-reset-keeps-buffer-loan", func(t *testing.T) {
		k := newKit(t)
		k.structItem(k.std, "Fixed", 0, true, false, field("base", k.tab.RawPtr(types.U8)))
		ft := k.named("Fixed")
		mi := k.tab.Mut(types.I32)
		fn := k.declare("Fixed.New", types.MemberKey("std", "Fixed", "New"), types.NoReceiver, nil, []types.Param{k.param("buf", mi)}, ft, types.EmptyErrors)
		fn.Flows.Sources = []types.Source{{Param: 1}}
		reset := k.method("Fixed", "Reset", types.ByMut, ft, nil, types.Void, types.EmptyErrors)
		reset.Flows.Ends = []types.ParamIndex{1}

		m := k.body(k.sig("F", nil, types.Void, types.EmptyErrors))
		buf := m.user("buf", types.I32, true)
		m.set(buf, use(imm(types.I32, 0)))
		s := m.temp(mi)
		m.set(s, mutRef(m.local(buf)))
		f := m.user("f", ft, true)
		nx := m.block()
		m.call(fn.Item, nil, []mir.Arg{argMove(m.local(s))}, m.local(f), nx)
		m.at(nx)
		m.end(s)

		tf := m.temp(k.tab.Mut(ft))
		m.set(tf, mutRef(m.local(f)))
		m.callv("Fixed.Reset", nil, argMove(m.local(tf)))
		m.end(tf)

		// Writing buf after Fixed.Reset while f is still used later must
		// conflict with f's exclusive loan on buf.
		bad := m.set(buf, use(imm(types.I32, 1)))
		m.useRef(m.local(f), ft)
		m.end(f, buf)
		m.ret(mir.ExitNormal)
		m.expect(t, m.check(t), diag.E0502, bad)
	})
}
