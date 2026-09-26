import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.Real.Tendsto.of.Gt_0
import Lemma.UniformExponentialMixing.Sum_AbsSub.le.MulMulCMixExpMulNeg2.of.Ge_0.StochasticVec.StochasticVec.In_ActorBox
import Lemma.UniformExponentialMixing.Any_And_All_EqToFunSemigroup.of.In_ActorBox
open Filter


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
-- given
  (h₀ : θ ∈ actor_box d r)
  (hMix : UniformExponentialMixing r Q) :
-- imply
  ∃! μ, InvariantLaw μ (Q θ) := by
-- proof
  obtain ⟨μ, hμ, hfix⟩ := UniformExponentialMixing.Any_And_All_EqToFunSemigroup.of.In_ActorBox h₀ hMix
  refine ⟨μ, (hMix.semigroup.fixed_iff_invariantLaw θ h₀ μ hμ).1 hfix, fun ν hν => ?_⟩
  have hνfix := (hMix.semigroup.fixed_iff_invariantLaw θ h₀ ν hν.toStochasticVec).2 hν
  have hle : ∀ t, 0 ≤ t → ∑ i, |ν i - μ i| ≤ hMix.cMix * Real.exp (-hMix.γ * t) * 2 := by
    intro t ht
    have h := UniformExponentialMixing.Sum_AbsSub.le.MulMulCMixExpMulNeg2.of.Ge_0.StochasticVec.StochasticVec.In_ActorBox h₀ hν.toStochasticVec hμ ht hMix
    rwa [hνfix t ht, hfix t ht] at h
  have h0 : ∑ i, |ν i - μ i| ≤ 0 := ge_of_tendsto (Real.Tendsto.of.Gt_0 hMix.γ_pos _ 2) (eventually_atTop.2 ⟨0, hle⟩)
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (ν i - μ i))).1 (le_antisymm h0 (Finset.sum_nonneg fun i _ => abs_nonneg _)) i (Finset.mem_univ i)
  linarith [abs_eq_zero.1 this]


-- created on 2026-09-26
