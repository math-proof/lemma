import Lemma.Nat.Add
open Nat


@[main, comm, mp, mpr]
private lemma right
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < c + b :=
-- proof
  Nat.sub_lt_iff_lt_add h


@[main, comm, mp, mpr]
private lemma main
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  a - b < c ↔ a < b + c := by
-- proof
  rw [right h]
  rw [Add.comm]


-- created on 2025-08-02
