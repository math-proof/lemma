import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.GeInv_0.is.Ge_0
import Lemma.Algebra.LeMulS.of.Le.Ge_0
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≥ 0) :
-- imply
  a / x ≤ b / x := by
-- proof
  have h₂ := GeInv_0.of.Ge_0 h₁
  have h₃ := LeMulS.of.Le.Ge_0 h₀ h₂
  repeat rw [Mul_Inv.eq.Div] at h₃
  assumption


-- created on 2025-03-01
