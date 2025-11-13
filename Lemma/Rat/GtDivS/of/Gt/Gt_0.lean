import Lemma.Nat.LtMulS.of.Lt.Gt_0
import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.GtInv_0.is.Gt_0
open Nat Rat


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
