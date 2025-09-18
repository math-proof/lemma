import Lemma.Algebra.Add
open Algebra


@[main, comm, mp, mpr]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < b + c :=
-- proof
  Nat.sub_lt_iff_lt_add h


@[main, comm, mp, mpr]
private lemma right
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < c + b := by
-- proof
  rw [Add.comm]
  apply Nat.sub_lt_iff_lt_add h


-- created on 2025-08-02
