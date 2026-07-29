import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.EqAbs_0.is.Eq_0 |
| comm | Int.Eq_0.is.EqAbs_0 |
| mp   | Int.Eq_0.of.EqAbs_0 |
| mpr  | Int.EqAbs_0.of.Eq_0 |
| mp.mt | Int.NeAbs_0.of.Ne_0 |
| mpr.mt | Int.Ne_0.of.NeAbs_0 |
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
