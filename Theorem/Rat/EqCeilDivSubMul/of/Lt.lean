module

public import Theorem.Nat.CeilSub.eq.Sub_Floor
public import Theorem.Nat.Ne_0.of.Gt
public import Theorem.Rat.FloorDiv.eq.Zero.of.Lt
public import Theorem.Rat.Sub_Div.eq.DivSubMul.of.Ne_0

public section

open Nat Rat


public theorem Rat.EqCeilDivSubMul.of.Lt
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {m n j : ℕ}
-- given
  (h : j < n) :
-- imply
  ⌈(m * n - j : α) / n⌉ = m := by
-- proof
  rw [DivSubMul.eq.Sub_Div.of.Ne_0]
  ·
    rw [CeilSub.eq.Sub_Floor]
    simp [FloorDiv.eq.Zero.of.Lt h]
  ·
    simp
    apply Ne_0.of.Gt h


-- created on 2025-11-08
