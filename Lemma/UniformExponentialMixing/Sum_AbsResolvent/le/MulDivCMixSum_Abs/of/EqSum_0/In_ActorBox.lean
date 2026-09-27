import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.UniformExponentialMixing.IntegrableOn.of.EqSum_0.In_ActorBox
open MeasureTheory


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
  ∑ i, |hMix.resolvent θ ξ i| ≤ hMix.cMix / hMix.γ * ∑ i, |ξ i| := by
-- proof
  have hint := UniformExponentialMixing.IntegrableOn.of.EqSum_0.In_ActorBox h₀ h₁ hMix
  have hcoord : ∀ i, IntegrableOn (fun t => hMix.semigroup.toFun θ t ξ i) (Set.Ioi 0) := fun i =>
    (ContinuousLinearMap.proj i : (S → ℝ) →L[ℝ] ℝ).integrable_comp hint
  have happly : ∀ i, (∫ t in Set.Ioi (0 : ℝ), hMix.semigroup.toFun θ t ξ) i = ∫ t in Set.Ioi (0 : ℝ), hMix.semigroup.toFun θ t ξ i := fun i =>
    ((ContinuousLinearMap.proj i : (S → ℝ) →L[ℝ] ℝ).integral_comp_comm hint).symm
  have hbound : IntegrableOn (fun t => hMix.cMix * (∑ i, |ξ i|) * Real.exp (-hMix.γ * t)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hMix.γ_pos).const_mul _
  calc
    _ = ∑ i, |∫ t in Set.Ioi (0 : ℝ), hMix.semigroup.toFun θ t ξ i| := by
      simp [UniformExponentialMixing.resolvent, happly]
    _ ≤ ∑ i, ∫ t in Set.Ioi (0 : ℝ), |hMix.semigroup.toFun θ t ξ i| :=
      Finset.sum_le_sum fun i _ => abs_integral_le_integral_abs
    _ = ∫ t in Set.Ioi (0 : ℝ), ∑ i, |hMix.semigroup.toFun θ t ξ i| :=
      (integral_finsetSum _ fun i _ => (hcoord i).abs).symm
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), hMix.cMix * (∑ i, |ξ i|) * Real.exp (-hMix.γ * t) := by
      refine setIntegral_mono_on (integrable_finsetSum _ fun i _ => (hcoord i).abs) hbound measurableSet_Ioi fun t ht => ?_
      linarith [hMix.mixing θ h₀ ξ h₁ t (le_of_lt ht)]
    _ = hMix.cMix / hMix.γ * ∑ i, |ξ i| := by
      rw [integral_const_mul]
      have h := integral_exp_mul_Ioi (a := -hMix.γ) (by linarith [hMix.γ_pos]) 0
      simp only [mul_zero, Real.exp_zero] at h
      rw [h]
      field_simp [hMix.γ_pos.ne']


-- created on 2026-09-26
