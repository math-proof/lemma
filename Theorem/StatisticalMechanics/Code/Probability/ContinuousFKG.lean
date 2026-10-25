/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Probability

set_option linter.unusedSectionVars false


theorem ContinuousFKG.integrable_of_bdd {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ := by
  refine (memLp_top_of_bound hf.aestronglyMeasurable C ?_).integrable le_top
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x)


theorem ContinuousFKG.comonotone_nonneg {f g : ℝ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (x y : ℝ) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with h | h
  · have h1 : 0 ≤ -(f x - f y) := by linarith [hf h]
    have h2 : 0 ≤ -(g x - g y) := by linarith [hg h]
    have := mul_nonneg h1 h2
    linarith [this, neg_mul_neg (f x - f y) (g x - g y)]
  · have h1 : 0 ≤ f x - f y := sub_nonneg.mpr (hf h)
    have h2 : 0 ≤ g x - g y := sub_nonneg.mpr (hg h)
    exact mul_nonneg h1 h2


theorem chebyshev_correlation_prob (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ x, |f x| ≤ Cf) (hgC : ∀ x, |g x| ≤ Cg)
    (hf : Monotone f) (hg : Monotone g) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC 0)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  set ν := μ.prod μ with hν
  
  have hA : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_fst).mul (hgm.comp measurable_fst)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hB : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_fst).mul (hgm.comp measurable_snd)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hC' : Integrable (fun z : ℝ × ℝ => f z.2 * g z.1) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_snd).mul (hgm.comp measurable_fst)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hD : Integrable (fun z : ℝ × ℝ => f z.2 * g z.2) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_snd).mul (hgm.comp measurable_snd)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  
  have hHnn : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂ν := by
    apply integral_nonneg
    intro z; exact ContinuousFKG.comonotone_nonneg hf hg z.1 z.2
  
  have hsplit : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂ν
      = (∫ z, f z.1 * g z.1 ∂ν) - (∫ z, f z.1 * g z.2 ∂ν)
        - (∫ z, f z.2 * g z.1 ∂ν) + (∫ z, f z.2 * g z.2 ∂ν) := by
    rw [show (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2))
        = (fun z => f z.1 * g z.1) - (fun z => f z.1 * g z.2)
          - (fun z => f z.2 * g z.1) + (fun z => f z.2 * g z.2) by funext z; simp; ring]
    rw [integral_add' (by exact (hA.sub hB).sub hC') hD,
        integral_sub' (hA.sub hB) hC', integral_sub' hA hB]
  rw [hsplit] at hHnn
  
  have eA : ∫ z, f z.1 * g z.1 ∂ν = ∫ x, f x * g x ∂μ := by
    rw [hν, integral_fun_fst (fun x => f x * g x)]; simp
  have eD : ∫ z, f z.2 * g z.2 ∂ν = ∫ x, f x * g x ∂μ := by
    rw [hν, integral_fun_snd (fun x => f x * g x)]; simp
  have eB : ∫ z, f z.1 * g z.2 ∂ν = (∫ x, f x ∂μ) * (∫ y, g y ∂μ) := by
    rw [hν, integral_prod_mul]
  have eC : ∫ z, f z.2 * g z.1 ∂ν = (∫ x, g x ∂μ) * (∫ y, f y ∂μ) := by
    rw [hν, show (fun z : ℝ × ℝ => f z.2 * g z.1) = (fun z : ℝ × ℝ => g z.1 * f z.2) by
      funext z; ring, integral_prod_mul]
  rw [eA, eB, eC, eD] at hHnn
  nlinarith [hHnn]


end Probability
end StatMech
