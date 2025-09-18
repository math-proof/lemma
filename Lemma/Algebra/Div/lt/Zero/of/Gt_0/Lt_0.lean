import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Algebra.LtInv_0.is.Lt_0
import Lemma.Algebra.Mul.lt.Zero.of.Gt_0.Lt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x y : α}
-- given
  (h₀ : x > 0)
  (h₁ : y < 0) :
-- imply
  x / y < 0 := by
-- proof
  have h₁ := LtInv_0.of.Lt_0 h₁
  have := Mul.lt.Zero.of.Gt_0.Lt_0 h₀ h₁
  rw [Mul_Inv.eq.Div] at this
  assumption


-- created on 2025-07-20
