module

public import Theorem.Rat.Div.ge.Zero.of.Ge_0.Ge_0
public import Theorem.Int.Ge_0

public section

open Int Rat


public theorem Rat.Div.ge.Zero
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℕ} :
-- imply
  (a : R) / (b : R) ≥ 0 := by
-- proof
  apply Div.ge.Zero.of.Ge_0.Ge_0 <;>
    apply Ge_0


-- created on 2025-07-06
