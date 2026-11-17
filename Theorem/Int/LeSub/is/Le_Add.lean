module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Int.LeSub.is.Le_Add.left
  [AddCommGroup α] [LE α] [AddLeftMono α]
-- given
  (a b c : α) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add'


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.LeSub.is.Le_Add |
| comm | Int.Le_Add.is.LeSub |
| mp   | Int.Le_Add.of.LeSub |
| mpr  | Int.LeSub.of.Le_Add |
| mp.comm | Int.GeAdd.of.Ge_Sub |
| mpr.comm | Int.Ge_Sub.of.GeAdd |
| comm.is | Int.Ge_Sub.is.GeAdd |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Int.LeSub.is.Le_Add
  [AddGroup α] [LE α] [AddRightMono α]
-- given
  (a b c : α) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  sub_le_iff_le_add



public theorem Int.Ge_Sub.of.GeAdd.left
  [AddCommGroup α] [LE α] [AddLeftMono α]
  {a b c : α} (h : a + b ≥ c) : c - a ≤ b :=
  (Int.LeSub.is.Le_Add.left a b c).mpr h

-- created on 2025-10-16
