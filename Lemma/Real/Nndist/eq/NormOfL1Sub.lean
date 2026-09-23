import Lemma.Matrix.OfL1.eq.Sub
open WithLp Matrix Metric NNReal


@[main]
private lemma main
  {S : Type u} [Fintype S]
-- given
  (a b : S → ℝ) :
-- imply
  (nndist (ofL1 a) (ofL1 b) : ℝ) = ‖ofL1 (a - b)‖ := by
-- proof
  rw [nndist_eq_nnnorm, coe_nnnorm, Matrix.OfL1.eq.Sub]


-- created on 2026-09-24
