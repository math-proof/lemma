import Lemma.Algebra.LtSub_1.of.Le.Gt_0
open Algebra


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : y ≥ x) :
-- imply
  y > x - 1 :=
-- proof
  LtSub_1.of.Le.Gt_0 h₀ h₁


-- created on 2025-05-05
