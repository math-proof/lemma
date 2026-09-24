import sympy.Basic
import sympy.stats.stochastic_process_types
open NNReal WithLp

@[main]
private lemma main
  {S : Type*} [Fintype S]
  {x : S → ℝ}
-- given
  (hx : StochasticVec x) :
-- imply
  ‖ofL1 x‖ = 1 := by
-- proof
  have hnorm : ‖ofL1 x‖ = ∑ s, |WithLp.ofLp (ofL1 x) s| := by
    simpa using (PiLp.norm_eq_sum (f := ofL1 x))
  rw [hnorm]
  have : WithLp.ofLp (ofL1 x) = x := by
    simp [ofL1]
  simp [this]
  have hsum : ∑ s, |x s| = ∑ s, x s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [abs_of_nonneg (hx.nonneg s)]
  rw [hsum, hx.rowsum]

-- created on 2026-09-19
