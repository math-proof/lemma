module

public import Theorem.Nat.Le.of.Lt_Add_1
public import Theorem.Nat.LtSub_1.of.Le.Gt_0

public section

open Nat


public theorem List.LengthTail.gt.Sub_1.of.GtLength.Gt_0
  {s : List α}
-- given
  (h₀ : i > 0)
  (h₁ : s.length > i) :
-- imply
  s.tail.length > i - 1 := by
-- proof
  match s with
  | .nil =>
    simp
    contradiction
  | head :: tail =>
    simp_all
    apply LtSub_1.of.Le.Gt_0.left h₀ h₁


-- created on 2025-05-05
