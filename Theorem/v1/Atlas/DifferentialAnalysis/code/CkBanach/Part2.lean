/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Normed.Group.Basic
import Instance.v1.Atlas.DifferentialAnalysis.code.CkBanach
open scoped ZeroAtInfty
open Filter Topology Finset


noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- Unfolding the `C¹` norm on `ContDiffZeroAtInfty n` as the supremum norm of
the function plus the sum over coordinates of the supremum norms of the
partial derivatives. -/
theorem ContDiffZeroAtInfty.norm_def (u : ContDiffZeroAtInfty n) :
    ‖u‖ = (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) +
      ∑ j : Fin n, ⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖ := by
  show ckNorm n 1 _ = _
  simp [ckNorm]

/-- The `C¹` norm on `ContDiffZeroAtInfty n` is nonnegative. -/
theorem ContDiffZeroAtInfty.c1_norm_nonneg (u : ContDiffZeroAtInfty n) :
    0 ≤ ‖u‖ := by
  rw [ContDiffZeroAtInfty.norm_def]
  apply add_nonneg
  · exact Real.iSup_nonneg (fun x => norm_nonneg _)
  · exact Finset.sum_nonneg (fun j _ => Real.iSup_nonneg (fun x => norm_nonneg _))

/-- The `C¹` norm of the zero element of `ContDiffZeroAtInfty n` is zero. -/
theorem ContDiffZeroAtInfty.c1_norm_zero : ‖(0 : ContDiffZeroAtInfty n)‖ = 0 := by
  show ckNorm n 1 _ = 0
  simp only [ckNorm]
  have hcoe : (0 : ContDiffZeroAtInfty n).toZeroAtInftyContinuousMap =
      (0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) := rfl
  rw [hcoe]
  have h0 : ∀ x : EuclideanSpace ℝ (Fin n),
      (0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) x = 0 := fun _ => rfl
  have hf0 : ∀ j : Fin n, ∀ x : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (⇑(0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ)) x
        (EuclideanSpace.single j 1) = 0 := by
    intro j x
    rw [show (⇑(0 : ZeroAtInftyContinuousMap (EuclideanSpace ℝ (Fin n)) ℂ) :
        EuclideanSpace ℝ (Fin n) → ℂ) = Function.const _ 0 from funext h0,
      fderiv_const]; rfl
  simp_rw [h0, hf0, norm_zero, ciSup_const, Finset.sum_const_zero, add_zero]


end TestFunctions
end
