module

public import Theorem.Nat.OfNat.eq.Cast
public import Theorem.Nat.LeCoeS.is.Le
public import Theorem.Int.Ge0Sub.is.Le
public import Theorem.Rat.Div.le.Zero.of.Le_0.Ge_0
public import Theorem.Nat.LeCeil.is.Le
public import Theorem.Int.EqToNat_0.of.Le_0

public section

open Int Nat Rat


public theorem Rat.EqToNatCeil_0.of.Le
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b d : ℕ}
-- given
  (h : a ≤ b) :
-- imply
  ⌈(a - b : α) / d⌉.toNat = 0 := by
-- proof
  have h := LeCoeS.of.Le (R := α) h
  have h := Ge0Sub.of.Le h
  have h_Ge_0 : (d : α) ≥ 0 := by simp
  have h_Le := Div.le.Zero.of.Le_0.Ge_0 h h_Ge_0
  apply EqToNat_0.of.Le_0
  apply Nat.LeCeil.of.Le
  rwa [OfNat.eq.Cast] at h_Le


-- created on 2025-05-05
