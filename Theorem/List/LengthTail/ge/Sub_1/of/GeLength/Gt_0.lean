module

public import Theorem.Nat.Le.of.LtSub_1
public import Theorem.Nat.Sub.gt.Zero.is.Gt
public import Theorem.List.LengthTail.gt.Sub_1.of.GtLength.Gt_0

public section

open List Nat


public theorem List.LengthTail.ge.Sub_1.of.GeLength.Gt_0
  {s : List α}
-- given
  (h₀ : i > 1)
  (h₁ : s.length ≥ i) :
-- imply
  s.tail.length ≥ i - 1 := by
-- proof
  apply Ge.of.Gt_Sub_1
  have h₁ := Gt_Sub_1.of.Ge.Gt_0 (show s.length > 0 by linarith) h₁
  apply LengthTail.gt.Sub_1.of.GtLength.Gt_0 _ h₁
  apply Sub.gt.Zero.of.Gt h₀


-- created on 2025-05-05
-- updated on 2025-05-06
