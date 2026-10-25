/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HormanderFundamental.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TemperedDistributions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
import Def.v1.Atlas.DifferentialAnalysis.code.TemperedDistributions
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
open scoped SchwartzMap LineDeriv Pointwise Manifold
open Distribution


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- Schwartz decay of the translated–reflected function `y ↦ φ(x − y)`: for every multi-index orders `k, l`, the weighted derivative norm is uniformly bounded in `y`. -/
theorem schwartzTranslateReflect_decay
    {n : ℕ}
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ k l : ℕ, ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun z => φ (x - z)) y‖ ≤ C := by
  intro k l


  let f : EuclideanSpace ℝ (Fin n) → ℂ := φ
  have hfg : (fun z => φ (x - z)) =
      (fun w => f (x + w)) ∘ (LinearIsometryEquiv.neg ℝ) := by
    ext z
    simp only [Function.comp, LinearIsometryEquiv.coe_neg, sub_eq_add_neg, f]

  have hnorm_eq : ∀ y, ‖iteratedFDeriv ℝ l (fun z => φ (x - z)) y‖ =
      ‖iteratedFDeriv ℝ l f (x - y)‖ := by
    intro y
    rw [hfg]
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
    rw [iteratedFDeriv_comp_add_left]
    simp only [LinearIsometryEquiv.coe_neg, ← sub_eq_add_neg]


  simp_rw [hnorm_eq]

  set S₀ := SchwartzMap.seminorm ℝ 0 l φ with hS₀_def
  set Sₖ := SchwartzMap.seminorm ℝ k l φ with hSₖ_def
  refine ⟨2 ^ (k - 1) * (‖x‖ ^ k * S₀ + Sₖ), fun y => ?_⟩
  have hx_nn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hxy_nn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
  have hS₀_nn : (0 : ℝ) ≤ S₀ := apply_nonneg _ _
  have hSₖ_nn : (0 : ℝ) ≤ Sₖ := apply_nonneg _ _

  have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
         _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _

  have hpow : ‖y‖ ^ k ≤ (‖x‖ + ‖x - y‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) htri k

  have hbin : (‖x‖ + ‖x - y‖) ^ k ≤ 2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) :=
    add_pow_le hx_nn hxy_nn k

  have hderiv_bound : ‖iteratedFDeriv ℝ l f (x - y)‖ ≤ S₀ := by
    have := SchwartzMap.le_seminorm ℝ 0 l φ (x - y)
    rwa [pow_zero, one_mul] at this

  have hxy_decay : ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ ≤ Sₖ :=
    SchwartzMap.le_seminorm ℝ k l φ (x - y)
  have hderiv_nn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ l f (x - y)‖ := norm_nonneg _
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖
      ≤ (‖x‖ + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ :=
        mul_le_mul_of_nonneg_right hpow hderiv_nn
    _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k + ‖x - y‖ ^ k) * ‖iteratedFDeriv ℝ l f (x - y)‖ :=
        mul_le_mul_of_nonneg_right hbin hderiv_nn
    _ = 2 ^ (k - 1) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖ +
        ‖x - y‖ ^ k * ‖iteratedFDeriv ℝ l f (x - y)‖) := by ring
    _ ≤ 2 ^ (k - 1) * (‖x‖ ^ k * S₀ + Sₖ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        exact add_le_add
          (mul_le_mul_of_nonneg_left hderiv_bound (pow_nonneg hx_nn _))
          hxy_decay

end DifferentialOperators
end
