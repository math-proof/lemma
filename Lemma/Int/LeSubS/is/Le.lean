import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LeSubS.is.Le |
| comm | Int.Le.is.LeSubS |
| mp   | Int.Le.of.LeSubS |
| mpr  | Int.LeSubS.of.Le |
| mp.comm | Int.Ge.of.GeSubS |
| mpr.comm | Int.GeSubS.of.Ge |
| comm.is | Int.GeSubS.is.Ge |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α]
  [LE α]
  [AddRightMono α]
-- given
  (x y c : α) :
-- imply
  x - c ≤ y - c ↔ x ≤ y :=
-- proof
  sub_le_sub_iff_right c


-- created on 2025-05-14
-- updated on 2025-09-30
