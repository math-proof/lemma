import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddCommGroup α]
-- given
  (d x y : α) :
-- imply
  y - d = x ↔ y = d + x := by
-- proof
  aesop


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.EqSub.is.Eq_Add |
| comm | Int.Eq_Add.is.EqSub |
| mp   | Int.Eq_Add.of.EqSub |
| mpr  | Int.EqSub.of.Eq_Add |
| mp.comm | Int.EqAdd.of.Eq_Sub |
| mpr.comm | Int.Eq_Sub.of.EqAdd |
| comm.is | Int.Eq_Sub.is.EqAdd |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α]
-- given
  (d x y : α) :
-- imply
  y - x = d ↔ y = d + x := by
-- proof
  aesop


-- created on 2025-04-26
