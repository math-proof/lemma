module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Nat.LtMulS.of.Lt.Gt_0
public import Theorem.Rat.Div.eq.Mul_Inv
public import Theorem.Rat.GtInv_0.is.Gt_0

public section

open Nat Rat


@[comm 2]
public theorem Rat.LtDivS.of.Lt.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a < b)
  (h₁ : x > 0) :
-- imply
  a / x < b / x := by
-- proof
  have := GtInv_0.of.Gt_0 h₁
  have := LtMulS.of.Lt.Gt_0 h₀ this
  repeat rw [Mul_Inv.eq.Div] at this
  assumption



public theorem Rat.GtDivS.of.Gt.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
  (h₀ : a > b)
  (h₁ : x > 0) :
  a / x > b / x :=
  Rat.LtDivS.of.Lt.Gt_0 (a := b) (b := a) h₀ h₁

-- created on 2024-11-25
-- updated on 2025-04-04
