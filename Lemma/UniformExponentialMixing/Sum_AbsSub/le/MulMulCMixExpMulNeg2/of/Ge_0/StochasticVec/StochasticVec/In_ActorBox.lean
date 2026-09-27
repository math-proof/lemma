import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.StochasticVec.Sum_AbsSub.le.Two.of.StochasticVec.StochasticVec


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
  {μ ν : S → ℝ}
  {t : ℝ}
-- given
  (h₀ : θ ∈ actor_box d r)
  (h₁ : StochasticVec μ)
  (h₂ : StochasticVec ν)
  (h₃ : 0 ≤ t)
  (hMix : UniformExponentialMixing r Q) :
-- imply
  ∑ i, |hMix.semigroup.toFun θ t μ i - hMix.semigroup.toFun θ t ν i| ≤ hMix.cMix * Real.exp (-hMix.γ * t) * 2 := by
-- proof
  have h := hMix.mixing θ h₀ (μ - ν) (by simp [Finset.sum_sub_distrib, h₁.rowsum, h₂.rowsum]) t h₃
  simp only [map_sub, Pi.sub_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left (StochasticVec.Sum_AbsSub.le.Two.of.StochasticVec.StochasticVec h₁ h₂) (mul_nonneg (by linarith [hMix.cMix_ge_one]) (Real.exp_pos _).le))


-- created on 2026-09-26
