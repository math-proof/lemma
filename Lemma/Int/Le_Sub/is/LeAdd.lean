import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddCommGroup α] [LE α] [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  b ≤ c - a ↔ a + b ≤ c :=
-- proof
  le_sub_iff_add_le'

/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Le_Sub.is.LeAdd |
| comm | Int.LeAdd.is.Le_Sub |
| mp   | Int.LeAdd.of.Le_Sub |
| mpr  | Int.Le_Sub.of.LeAdd |
| mp.comm | Int.Ge_Add.of.GeSub |
| mpr.comm | Int.GeSub.of.Ge_Add |
| comm.is | Int.GeSub.is.Ge_Add |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α] [LE α] [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  a ≤ c - b ↔ a + b ≤ c :=
-- proof
  le_sub_iff_add_le


-- created on 2024-11-27
