module

public import Theorem.List.LengthFlatten.eq.MulLength.of.All_EqLength
public import Theorem.Nat.AddMul.lt.Mul.of.Lt.Lt

public section

open List Nat


public theorem List.AddMul.lt.LengthFlatten.of.Lt.GtLength.All_EqLength
  {i j n : ℕ}
  {s : List (List α)}
-- given
  (h₀ : ∀ l ∈ s, l.length = n)
  (h₁ : s.length > i)
  (h₂ : j < n) :
-- imply
  i * n + j < s.flatten.length := by
-- proof
  rw [LengthFlatten.eq.MulLength.of.All_EqLength h₀]
  apply AddMul.lt.Mul.of.Lt.Lt <;>
    assumption


-- created on 2025-06-28
