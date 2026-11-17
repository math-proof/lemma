module

public import Theorem.Nat.Le_Sub_1.of.Lt

public section

open Nat


public theorem Nat.Le_Sub_1
-- given
  (i : Fin n) :
-- imply
  i ≤ n - 1 := by
-- proof
  have := i.isLt
  apply Le_Sub_1.of.Lt this


-- created on 2025-05-07
-- updated on 2025-06-07
