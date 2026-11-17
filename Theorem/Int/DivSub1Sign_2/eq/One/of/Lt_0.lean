module

public import Theorem.Int.Sign.eq.Neg1.of.Lt_0

public section

open Int


public theorem Int.DivSub1Sign_2.eq.One.of.Lt_0
  {n : ℤ}
-- given
  (h : n < 0) :
-- imply
  (1 - sign n) / 2 = 1 := by
-- proof
  have := Sign.eq.Neg1.of.Lt_0 h
  rw [this]
  simp


-- created on 2025-06-26
