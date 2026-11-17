module

public import Theorem.Rat.LeDivS.of.Le.Ge_0
public import Theorem.Rat.EqDiv0_0

public section

open Rat


public theorem Rat.Div.ge.Zero.of.Ge_0.Ge_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := GeDivS.of.Ge.Ge_0 h₀ h₁
  simp only [EqDiv0_0] at h
  assumption


-- created on 2025-01-14
