import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Le0Sub.is.Ge |
| comm | Int.Ge.is.Le0Sub |
| mp   | Int.Ge.of.Le0Sub |
| mpr  | Int.Le0Sub.of.Ge |
| mp.comm | Int.Le.of.Le0Sub |
| mpr.comm | Int.Le0Sub.of.Le |
| comm.is | Int.Le0Sub.is.Le |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
  {x y : α} :
-- imply
  x - y ≥ 0 ↔ x ≥ y :=
-- proof
  sub_nonneg


-- created on 2018-07-03
-- updated on 2023-03-25
