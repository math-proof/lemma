import Lemma.Algebra.LtDivS.of.Lt.Gt_0
import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.EqDivMul.of.Ne_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {n d x : α}
-- given
  (h₀ : n < x * d)
  (h₁ : d > 0) :
-- imply
  n / d < x := by
-- proof
  have := LtDivS.of.Lt.Gt_0 h₀ h₁
  have h_Ne_0 := Ne.of.Gt h₁
  rwa [EqDivMul.of.Ne_0 h_Ne_0] at this


-- created on 2025-03-30
