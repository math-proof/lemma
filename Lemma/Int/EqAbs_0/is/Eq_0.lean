import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.EqAbs\_0.is.Eq\_0 |
| comm | Int.Eq\_0.is.EqAbs\_0 |
| mp   | Int.Eq\_0.of.EqAbs\_0 |
| mpr  | Int.EqAbs\_0.of.Eq\_0 |
| mp.mt | Int.NeAbs\_0.of.Ne\_0 |
| mpr.mt | Int.Ne\_0.of.NeAbs\_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α]
  [LinearOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (a : α) :
-- imply
  |a| = 0 ↔ a = 0 :=
-- proof
  abs_eq_zero


-- created on 2025-08-02
