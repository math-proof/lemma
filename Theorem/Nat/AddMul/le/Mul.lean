module

public import Theorem.Nat.AddMul.le.Mul.of.Lt

public section

open Nat


public theorem Nat.AddMul.le.Mul
  {n : ℕ}
  {i : Fin n} :
-- imply
  m * i + m ≤ m * n := by
-- proof
  have hi := i.isLt
  apply AddMul.le.Mul.of.Lt hi


-- created on 2025-05-06
-- updated on 2025-05-31
