import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {hMix : UniformExponentialMixing r Q}
  {θ θ' : EuclideanVec d}
  {μ μ' : S → ℝ}
-- given
  (h₀ : θ ∈ actor_box d r)
  (h₁ : θ' ∈ actor_box d r)
  (h₂ : InvariantLaw μ (Q θ))
  (h₃ : InvariantLaw μ' (Q θ'))
  (hR : FrozenResolventWitness r Q hMix) :
-- imply
  ∑ i, |μ i - μ' i| ≤ hMix.cMix * hMix.hQ.lQ / hMix.γ * dist θ θ' := by
-- proof
  have hη : ∑ i, (μ - μ') i = 0 := by simp [Finset.sum_sub_distrib, h₂.rowsum, h₃.rowsum]
  have hξ : (μ - μ') ᵥ* Q θ = -(μ' ᵥ* Q θ - μ' ᵥ* Q θ') := by
    rw [Matrix.sub_vecMul, h₂.invariant, h₃.invariant]
    simp
  have hlip := hMix.hQ.lipschitz_on_box.lipschitz θ h₀ θ' h₁ μ'
  rw [show ∑ i, |μ' i| = 1 by rw [← h₃.rowsum]; exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (h₃.nonneg i), mul_one] at hlip
  have hbound := hR.bound θ h₀ ((μ - μ') ᵥ* Q θ) (GeneratorMatrix.Sum_GetVecMul.eq.Zero.of.GeneratorMatrix (hMix.hQ.generator_on_box θ h₀) _)
  rw [hR.right_inverse θ h₀ _ hη, hξ] at hbound
  simp only [Pi.neg_apply, abs_neg, Pi.sub_apply] at hbound
  calc
    _ ≤ hMix.cMix / hMix.γ * ∑ i, |(μ' ᵥ* Q θ) i - (μ' ᵥ* Q θ') i| := by simpa using hbound
    _ ≤ hMix.cMix / hMix.γ * (hMix.hQ.lQ * dist θ θ') :=
      mul_le_mul_of_nonneg_left (by simpa using hlip) (div_nonneg (by linarith [hMix.cMix_ge_one]) hMix.γ_pos.le)
    _ = _ := by ring


-- created on 2026-09-26
