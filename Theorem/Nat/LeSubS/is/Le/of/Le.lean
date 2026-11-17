module

public import Theorem.Nat.EqAddSub.of.Ge

public section

open Nat


public theorem Nat.LeSubS.is.Le.of.Le
-- given
  (h : z ≤ y)
  (x : ℕ) :
-- imply
  x - z ≤ y - z ↔ x ≤ y := by
-- proof
  simp
  rw [EqAddSub.of.Ge h]


-- created on 2025-05-14
