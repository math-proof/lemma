import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.EqMulDiv.of.Ne_0
import Lemma.Algebra.LtMulS.of.Lt.Gt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a b : α}
-- given
  (h₀ : a / x < b / x)
  (h₁ : x > 0) :
-- imply
  a < b := by
-- proof
  have := LtMulS.of.Lt.Gt_0 h₀ h₁
  have h₁ := Ne.of.Gt h₁
  repeat rw [EqMulDiv.of.Ne_0 h₁] at this
  assumption


-- created on 2025-03-30
