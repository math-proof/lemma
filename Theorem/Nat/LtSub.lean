module

public import Theorem.Nat.LtSub.of.Lt

public section

open Nat


public theorem Nat.LtSub
-- given
  (j : Fin n)
  (i : ℕ) :
-- imply
  j - i < n := by
-- proof
  apply LtSub.of.Lt
  apply j.isLt


-- created on 2025-06-21
