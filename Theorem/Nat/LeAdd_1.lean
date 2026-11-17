module

public import Theorem.Nat.LeAdd_1.of.Lt

public section

open Nat


public theorem Nat.LeAdd_1
  {n : ℕ}
  -- given
  (i : Fin n) :
-- imply
  i + 1 ≤ n := by
-- proof
  apply LeAdd_1.of.Lt
  simp


-- created on 2025-05-06
-- updated on 2025-06-18
