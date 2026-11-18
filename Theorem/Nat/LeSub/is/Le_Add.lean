module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeSub.is.Le_Add |
| comm | Nat.Le_Add.is.LeSub |
| mp   | Nat.Le_Add.of.LeSub |
| mpr  | Nat.LeSub.of.Le_Add |
| mp.comm | Nat.GeAdd.of.Ge_Sub |
| mpr.comm | Nat.Ge_Sub.of.GeAdd |
| comm.is | Nat.Ge_Sub.is.GeAdd |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Nat.LeSub.is.Le_Add
-- given
  (a b c : ℕ) :
-- imply
  c - b ≤ a ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add


@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Nat.LeSub.is.Le_Add.left
-- given
  (a b c : ℕ) :
-- imply
  c - a ≤ b ↔ c ≤ a + b :=
-- proof
  Nat.sub_le_iff_le_add'



public theorem Nat.GeAdd.of.Ge_Sub
  {a b c : ℕ} (h : c ≥ a - b) : c + b ≥ a :=
  (Nat.LeSub.is.Le_Add c b a).mp h

public theorem Nat.LeSub.of.Le_Add
  {a b c : ℕ}
  (h : c ≤ a + b) :
  c - b ≤ a :=
  (Nat.LeSub.is.Le_Add a b c).mpr h


-- created on 2024-11-27
-- updated on 2026-10-26
