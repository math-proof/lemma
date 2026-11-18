module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| --- | --- |
| path | Nat.Le_Sub.is.LeAdd.of.Le |
| comm | Nat.LeAdd.is.Le_Sub.of.Le |
| mp  | Nat.LeAdd.of.Le_Sub.Le |
| mpr   | Nat.Le_Sub.of.LeAdd.Le |
| mp.comm | Nat.Ge_Add.of.GeSub.Le |
| mpr.comm | Nat.GeSub.of.Ge_Add.Le |
| comm.is 1 | Nat.GeSub.is.Ge_Add.of.Ge |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is 1]
public theorem Nat.Le_Sub.is.LeAdd.of.Le
  {b c : ℕ}
-- given
  (h : b ≤ c)
  (a : ℕ) :
-- imply
  a ≤ c - b ↔ a + b ≤ c :=
-- proof
  Nat.le_sub_iff_add_le h


@[comm, mp, mpr, mp.comm, mpr.comm, comm.is 1]
public theorem Nat.Le_Sub.is.LeAdd.of.Le.left
  {a c : ℕ}
-- given
  (h : a ≤ c)
  (b : ℕ):
-- imply
  b ≤ c - a ↔ a + b ≤ c :=
-- proof
  Nat.le_sub_iff_add_le' h



public theorem Nat.Ge_Add.of.GeSub.Le
  {b c a : ℕ}
  (h₁ : a ≥ c - b)
  (h₂ : b ≤ c) :
  a + b ≥ c := by
  rw [ge_iff_le] at h₁ ⊢
  calc
    c = c - b + b := (Nat.sub_add_cancel h₂).symm
    _ ≤ a + b := Nat.add_le_add_right h₁ b

public theorem Nat.GeSub.of.Ge_Add.left
  {a b c : ℕ}
  (h : a ≥ b + c) :
  a - b ≥ c := by
  rw [ge_iff_le] at h ⊢
  have hb : b ≤ a := Nat.le_trans (Nat.le_add_right b c) h
  exact (Nat.le_sub_iff_add_le hb).mpr (by rw [Nat.add_comm]; exact h)


-- created on 2025-06-21
