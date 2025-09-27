import Lemma.Algebra.LeMulS.of.Le.Gt_0
import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.EqMulDiv.of.Ne_0
open Algebra


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a b : α}
-- given
  (h₀ : a / x ≤ b / x)
  (h₁ : x > 0) :
-- imply
  a ≤ b := by
-- proof
  have := LeMulS.of.Le.Gt_0 h₀ h₁
  have h₁ := Ne.of.Gt h₁
  repeat rw [EqMulDiv.of.Ne_0 h₁] at this
  assumption


-- created on 2025-03-30
