module

public import Theorem.List.Tail.eq.Drop_1
public import Theorem.List.LengthTail.ge.Sub_1.of.GeLength.Gt_0

public section

open List


public theorem List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
  {s : List α}
-- given
  (h₀ : i > 1)
  (h₁ : s.length ≥ i) :
-- imply
  (s.drop 1).length ≥ i - 1 := by
-- proof
  rw [Drop_1.eq.Tail]
  apply LengthTail.ge.Sub_1.of.GeLength.Gt_0 h₀ h₁


-- created on 2025-05-06
