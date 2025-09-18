import Lemma.Algebra.Lt.of.Le_Sub_1.Gt_0
open Algebra


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : y - 1 ≥ x) :
-- imply
  y > x :=
-- proof
  Lt.of.Le_Sub_1.Gt_0 h₀ h₁


-- created on 2025-05-07
