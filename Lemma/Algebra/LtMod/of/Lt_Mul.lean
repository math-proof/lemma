import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Gt_0.of.GtMul
open Algebra


@[main]
private lemma main
  {n k d : ℕ}
-- given
  (h : n < k * d) :
-- imply
  n % d < d :=
-- proof
  (LtMod.of.Gt_0 ∘ Gt_0.of.GtMul) h _


-- created on 2025-10-05
