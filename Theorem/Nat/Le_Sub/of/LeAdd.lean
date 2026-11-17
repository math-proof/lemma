module

public import Theorem.Nat.Le_Sub.is.LeAdd.of.Le

public section

open Nat


@[comm 1]
public theorem Nat.Le_Sub.of.LeAdd
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b := by
-- proof
  have : b ≤ c := by linarith
  exact (Nat.Le_Sub.is.LeAdd.of.Le this a).mpr h


@[comm 1]
public theorem Nat.Le_Sub.of.LeAdd.left
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  b ≤ c - a := by
-- proof
  have : a ≤ c := by linarith
  exact (Nat.Le_Sub.is.LeAdd.of.Le.left this b).mpr h


-- created on 2025-08-02
-- updated on 2025-10-16
