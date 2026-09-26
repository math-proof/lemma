import sympy.stats.stochastic_process
open WithLp PiLp Metric


@[main]
private lemma main
  {S : Type*} [Fintype S] :
-- imply
  (Simplex S) ⊆ closedBall (0 : l1Space S) 1 := by
-- proof
  intro x hx
  have hx' : StochasticVec (WithLp.ofLp x) := hx
  have : ‖x‖ = ∑ s, |WithLp.ofLp x s| := (by simpa using (PiLp.norm_eq_sum (f := x)) : ‖x‖ = ∑ s, |WithLp.ofLp x s|)
  have hsum : ∑ s, |WithLp.ofLp x s| = ∑ s, WithLp.ofLp x s := by
    apply Finset.sum_congr rfl
    intro s _
    exact abs_of_nonneg (hx'.nonneg s)
  have : ‖x‖ = 1 := by
    rw [this, hsum, hx'.rowsum]
  simp [this]

-- created on 2026-09-19
