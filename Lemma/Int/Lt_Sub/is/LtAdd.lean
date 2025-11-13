import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddCommGroup α] [LT α] [AddLeftStrictMono α]
-- given
  (a b c : α) :
-- imply
  b < c - a ↔ a + b < c :=
-- proof
  lt_sub_iff_add_lt'

/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Lt_Sub.is.LtAdd |
| comm | Int.LtAdd.is.Lt_Sub |
| mp   | Int.LtAdd.of.Lt_Sub |
| mpr  | Int.Lt_Sub.of.LtAdd |
| mp.comm | Int.Gt_Add.of.GtSub |
| mpr.comm | Int.GtSub.of.Gt_Add |
| comm.is | Int.GtSub.is.Gt_Add |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddCommGroup α] [LT α] [AddRightStrictMono α]
-- given
  (a b c : α) :
-- imply
  a < c - b ↔ a + b < c :=
-- proof
  lt_sub_iff_add_lt


-- created on 2025-11-13
