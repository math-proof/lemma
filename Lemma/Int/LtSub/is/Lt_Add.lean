import sympy.Basic


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddCommGroup α]
  [LT α]
  [AddLeftStrictMono α]
-- given
  (a b c : α) :
-- imply
  a - b < c ↔ a < b + c :=
-- proof
  sub_lt_iff_lt_add'

/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtSub.is.Lt_Add |
| comm | Int.Lt_Add.is.LtSub |
| mp   | Int.Lt_Add.of.LtSub |
| mpr  | Int.LtSub.of.Lt_Add |
| mp.comm | Int.GtAdd.of.Gt_Sub |
| mpr.comm | Int.Gt_Sub.of.GtAdd |
| comm.is | Int.Gt_Sub.is.GtAdd |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α]
  [LT α]
  [AddRightStrictMono α]
-- given
  (a b c : α) :
-- imply
  a - c < b ↔ a < b + c :=
-- proof
  sub_lt_iff_lt_add


-- created on 2025-11-13
