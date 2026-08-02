import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Ge0Sub.is.Le |
| comm | Int.Le.is.Ge0Sub |
| mp   | Int.Le.of.Ge0Sub |
| mpr  | Int.Ge0Sub.of.Le |
| mp.comm | Int.Ge.of.Ge0Sub |
| mpr.comm | Int.Ge0Sub.of.Ge |
| comm.is | Int.Ge0Sub.is.Ge |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {x y : α} :
-- imply
  x - y ≤ 0 ↔ x ≤ y :=
-- proof
  sub_nonpos


-- created on 2025-03-15
-- updated on 2026-08-02
