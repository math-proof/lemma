/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CkBanach
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Def.v1.Atlas.DifferentialAnalysis.code.CkBanachFix
open scoped ZeroAtInfty
open Filter Topology Finset


noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- Triangle inequality for the `C^1₀` norm on `ContDiffZeroAtInfty n`. -/
lemma ContDiffZeroAtInfty.c1_norm_add_le (u v : ContDiffZeroAtInfty n) :
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  show ckNorm n 1 _ ≤ ckNorm n 1 _ + ckNorm n 1 _
  simp only [ckNorm]
  have hudiff := u.differentiable
  have hvdiff := v.differentiable
  have hcoe_add : ∀ x, (u + v).toZeroAtInftyContinuousMap x =
      u.toZeroAtInftyContinuousMap x + v.toZeroAtInftyContinuousMap x := fun _ => rfl
  have hcoe_add_fn : (⇑(u + v).toZeroAtInftyContinuousMap : _ → ℂ) =
      ⇑u.toZeroAtInftyContinuousMap + ⇑v.toZeroAtInftyContinuousMap :=
    funext hcoe_add
  have hfderiv_add : ∀ j x,
      fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) =
      fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) +
      fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) := by
    intro j x
    rw [hcoe_add_fn, fderiv_add (hudiff x) (hvdiff x), ContinuousLinearMap.add_apply]
  have h1 : (⨆ x, ‖(u + v).toZeroAtInftyContinuousMap x‖) ≤
      (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) +
      (⨆ x, ‖v.toZeroAtInftyContinuousMap x‖) :=
    ciSup_le fun x => (hcoe_add x ▸ norm_add_le _ _).trans
      (add_le_add (u.norm_apply_le_iSup x) (v.norm_apply_le_iSup x))
  have h2 : ∀ j : Fin n,
      (⨆ x, ‖fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) ≤
      (⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) +
      (⨆ x, ‖fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) :=
    fun j => ciSup_le fun x => (hfderiv_add j x ▸ norm_add_le _ _).trans
      (add_le_add (u.norm_deriv_apply_le_iSup j x) (v.norm_deriv_apply_le_iSup j x))
  have h3 : (∑ j : Fin n, ⨆ x,
      ‖fderiv ℝ (⇑(u + v).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) ≤
      (∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) +
      (∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑v.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => h2 j
  linarith

/-- Scalar homogeneity of the `C^1₀` norm: `‖c • u‖ = ‖c‖ * ‖u‖`. -/
lemma ContDiffZeroAtInfty.c1_norm_smul (c : ℂ) (u : ContDiffZeroAtInfty n) :
    ‖c • u‖ = ‖c‖ * ‖u‖ := by
  show ckNorm n 1 _ = ‖c‖ * ckNorm n 1 _
  simp only [ckNorm]
  have hudiff := u.differentiable
  have hcoe_smul_fn : (⇑(c • u).toZeroAtInftyContinuousMap : _ → ℂ) =
      c • ⇑u.toZeroAtInftyContinuousMap := funext (fun _ => rfl)
  have hcoe_smul : ∀ x, (c • u).toZeroAtInftyContinuousMap x =
      c • u.toZeroAtInftyContinuousMap x := fun _ => rfl
  have hfderiv_smul : ∀ j x,
      fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) =
      c • fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1) := by
    intro j x
    rw [hcoe_smul_fn, fderiv_const_smul (hudiff x) c, ContinuousLinearMap.smul_apply]
  have h_val : (⨆ x, ‖(c • u).toZeroAtInftyContinuousMap x‖) =
      ‖c‖ * (⨆ x, ‖u.toZeroAtInftyContinuousMap x‖) := by
    have : (fun x => ‖(c • u).toZeroAtInftyContinuousMap x‖) =
        (fun x => ‖c‖ * ‖u.toZeroAtInftyContinuousMap x‖) :=
      funext fun x => by rw [hcoe_smul, norm_smul]
    rw [this, ← Real.mul_iSup_of_nonneg (norm_nonneg c)]
  have h_deriv : ∀ j : Fin n,
      (⨆ x, ‖fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) =
      ‖c‖ * (⨆ x, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) := by
    intro j
    have : (fun x => ‖fderiv ℝ (⇑(c • u).toZeroAtInftyContinuousMap) x
        (EuclideanSpace.single j 1)‖) =
        (fun x => ‖c‖ * ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x
          (EuclideanSpace.single j 1)‖) :=
      funext fun x => by rw [hfderiv_smul, norm_smul]
    rw [this, ← Real.mul_iSup_of_nonneg (norm_nonneg c)]
  rw [h_val]
  simp_rw [h_deriv]
  rw [← Finset.mul_sum, ← mul_add]

/-- Separation: the `C^1₀` norm vanishes iff the element is zero. -/
lemma ContDiffZeroAtInfty.c1_norm_eq_zero_iff (u : ContDiffZeroAtInfty n) :
    ‖u‖ = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h' : ckNorm n 1 ⇑u.toZeroAtInftyContinuousMap = 0 := h
    simp only [ckNorm] at h'
    have h_nn_val := Real.iSup_nonneg fun x => norm_nonneg (u.toZeroAtInftyContinuousMap x)
    have h_nn_sum : 0 ≤ ∑ j : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖ :=
      Finset.sum_nonneg fun j _ =>
        Real.iSup_nonneg fun x => norm_nonneg
          (fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1))
    have h_val_zero : ⨆ x, ‖u.toZeroAtInftyContinuousMap x‖ = 0 := by linarith
    have hpw : ∀ x, u.toZeroAtInftyContinuousMap x = 0 := by
      intro x
      have hle := u.norm_apply_le_iSup x
      rw [h_val_zero] at hle
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    exact ContDiffZeroAtInfty.toC0_injective (DFunLike.ext _ _ hpw)
  · intro h; rw [h]; exact ContDiffZeroAtInfty.c1_norm_zero

/-- Core data for the `NormedSpace` structure on `ContDiffZeroAtInfty n`. -/
lemma ContDiffZeroAtInfty.normedSpaceCore :
    NormedSpace.Core ℂ (ContDiffZeroAtInfty n) where
  norm_nonneg := ContDiffZeroAtInfty.c1_norm_nonneg
  norm_smul := ContDiffZeroAtInfty.c1_norm_smul
  norm_triangle := ContDiffZeroAtInfty.c1_norm_add_le
  norm_eq_zero_iff := ContDiffZeroAtInfty.c1_norm_eq_zero_iff

end TestFunctions
end
