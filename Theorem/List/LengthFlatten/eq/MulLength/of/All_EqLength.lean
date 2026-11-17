module

public import Theorem.Nat.MulAdd.eq.AddMulS
public import Theorem.Nat.Add

public section

open Nat


public theorem List.LengthFlatten.eq.MulLength.of.All_EqLength
  {n : ℕ}
  {s : List (List α)}
-- given
  (h : ∀ l ∈ s, l.length = n) :
-- imply
  s.flatten.length = s.length * n := by
-- proof
  induction s with
  | nil =>
    simp_all
  | cons s₀ s ih =>
    simp_all
    rw [MulAdd.eq.AddMulS]
    simp
    rw [Nat.Add.Comm]


-- created on 2025-06-28
