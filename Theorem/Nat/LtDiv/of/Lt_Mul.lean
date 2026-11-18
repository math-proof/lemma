module

public import Theorem.Nat.Mul

public section

open Nat


public theorem Nat.LtDiv.of.Lt_Mul.left
  {k n m : ℕ}
-- given
  (h : k < n * m) :
-- imply
  k / n < m :=
-- proof
  Nat.div_lt_of_lt_mul h


public theorem Nat.LtDiv.of.Lt_Mul
  {k n m : ℕ}
-- given
  (h : k < m * n) :
-- imply
  k / n < m := by
-- proof
  apply LtDiv.of.Lt_Mul.left
  rwa [Nat.Mul.Comm]


-- created on 2025-05-29
-- updated on 2025-07-08
