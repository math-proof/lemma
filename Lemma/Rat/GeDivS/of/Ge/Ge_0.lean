import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Rat.GeInv_0.is.Ge_0
import Lemma.Int.GeMulS.of.Ge.Ge_0
open Algebra Rat Int


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x ≥ 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have := GeInv_0.of.Ge_0 h₁
  have := GeMulS.of.Ge.Ge_0 h₀ this
  repeat rw [Mul_Inv.eq.Div] at this
  assumption


-- created on 2025-01-14
-- updated on 2025-03-30
