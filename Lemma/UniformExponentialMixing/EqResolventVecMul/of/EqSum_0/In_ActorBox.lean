import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix
import Lemma.Real.Norm.le.Sum_Abs
import Lemma.Real.Tendsto.of.Gt_0
import Lemma.UniformExponentialMixing.HasDerivWithinAt.of.Ge_0.In_ActorBox
import Lemma.UniformExponentialMixing.ToFunSemigroupVecMul.eq.VecMulToFunSemigroup.of.Ge_0.In_ActorBox
import Lemma.UniformExponentialMixing.IntegrableOn.of.EqSum_0.In_ActorBox
open Matrix Filter MeasureTheory Topology


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
  {ξ : S → ℝ}
-- given
  (h₀ : θ ∈ actor_box d r)
  (h₁ : ∑ i, ξ i = 0)
  (hMix : UniformExponentialMixing r Q) :
-- imply
  hMix.resolvent θ (ξ ᵥ* Q θ) = ξ := by
-- proof
  let T := hMix.semigroup.toFun θ
  have hint := UniformExponentialMixing.IntegrableOn.of.EqSum_0.In_ActorBox h₀ (GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix (hMix.hQ.generator_on_box θ h₀) ξ) hMix
  have hcont := (hMix.solves_equation θ h₀ ξ).cont
  have hcontq := (hMix.solves_equation θ h₀ (ξ ᵥ* Q θ)).cont
  have htend : Tendsto (fun t => T t ξ) atTop (𝓝 0) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (Real.Tendsto.of.Gt_0 hMix.γ_pos hMix.cMix (∑ i, |ξ i|)))
    filter_upwards [eventually_ge_atTop 0] with t ht
    simpa using (Real.Norm.le.Sum_Abs _).trans (hMix.mixing θ h₀ ξ h₁ t ht)
  have hinterval : ∀ b, 0 ≤ b → ∫ s in (0 : ℝ)..b, T s (ξ ᵥ* Q θ) = T b ξ - ξ := by
    intro b hb
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hb hcont.continuousOn
      (fun x hx => by
        rw [UniformExponentialMixing.ToFunSemigroupVecMul.eq.VecMulToFunSemigroup.of.Ge_0.In_ActorBox h₀ hx.1.le hMix ξ]
        exact (UniformExponentialMixing.HasDerivWithinAt.of.Ge_0.In_ActorBox h₀ hx.1.le hMix ξ).mono Set.Ioi_subset_Ici_self)
      (hcontq.continuousOn.intervalIntegrable_of_Icc hb)
    rw [h, hMix.semigroup.map_zero' θ, ContinuousLinearMap.id_apply]
  have h₂ : Tendsto (fun b => ∫ s in (0 : ℝ)..b, T s (ξ ᵥ* Q θ)) atTop (𝓝 (0 - ξ)) := by
    refine (htend.sub_const ξ).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with b hb
    exact (hinterval b hb).symm
  have := tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id) h₂
  change -(∫ s in Set.Ioi (0 : ℝ), T s (ξ ᵥ* Q θ)) = ξ
  rw [this]
  simp


-- created on 2026-09-26
