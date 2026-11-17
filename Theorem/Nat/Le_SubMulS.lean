module

public import Theorem.Nat.Le_SubMulS.of.Lt

public section

open Nat


public theorem Nat.Le_SubMulS.left
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ m * n - m * i := by
-- proof
  have hi := i.isLt
  apply Le_SubMulS.of.Lt.left hi


public theorem Nat.Le_SubMulS
  {m n : ℕ}
  {i : Fin n} :
-- imply
  m ≤ n * m - i * m := by
-- proof
  have hi := i.isLt
  apply Le_SubMulS.of.Lt hi


-- created on 2025-05-06
-- updated on 2025-05-31
