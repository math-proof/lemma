module

public import Mathlib

public section


public theorem Nat.LtSubS_1.of.Lt.Ne_0
  {n m : ℕ}
  -- given
  (h₀ : n ≠ 0)
  (h₁ : n < m) :
-- imply
  n - 1 < m - 1 := by
-- proof
  apply Nat.pred_lt_pred h₀
  simpa


-- created on 2025-10-05
