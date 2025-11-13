import Lemma.Nat.LtMulS.of.Lt.Gt_0
import Lemma.Rat.Div.eq.Mul_Inv
import Lemma.Rat.GtInv_0.is.Gt_0
open Nat Rat


@[main, comm 2]
private lemma main
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


-- created on 2024-11-25
-- updated on 2025-04-04
