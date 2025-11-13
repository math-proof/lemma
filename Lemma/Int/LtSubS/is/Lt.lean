import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtSubS.is.Lt |
| comm | Int.Lt.is.LtSubS |
| mp   | Int.Lt.of.LtSubS |
| mpr  | Int.LtSubS.of.Lt |
| mp.comm | Int.Gt.of.GtSubS |
| mpr.comm | Int.GtSubS.of.Gt |
| comm.is | Int.GtSubS.is.Gt |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddGroup α]
  [LT α]
  [AddRightStrictMono α]
-- given
  (x y c : α) :
-- imply
  x - c < y - c ↔ x < y :=
-- proof
  sub_lt_sub_iff_right c


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
-- given
  (a b c : α) :
-- imply
  a - b < a - c ↔ c < b :=
-- proof
  sub_lt_sub_iff_left a


-- created on 2025-09-30
