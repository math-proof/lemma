import Lemma.Algebra.GtMulS.of.Gt.Gt_0
import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.GtInv_0.is.Gt_0
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
  (h₀ : a > b)
  (h₁ : x > 0) :
-- imply
  a / x > b / x := by
-- proof
  have h₂ := GtInv_0.of.Gt_0 h₁
  have h₃ := GtMulS.of.Gt.Gt_0 h₀ h₂
  repeat rw [Mul_Inv.eq.Div] at h₃
  assumption


-- created on 2024-11-25
