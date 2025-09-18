import Lemma.Algebra.LeInvS.of.Ge.Gt_0
open Algebra


@[main]
private lemma main
  [LinearOrderedField α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x ≥ a) :
-- imply
  a⁻¹ ≥ x⁻¹ :=
-- proof
  LeInvS.of.Ge.Gt_0 h₀ h₁


-- created on 2025-03-15
