/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

@[simp] theorem constantRadialTensorTent_boundaryPoint (k : Nat) :
    constantRadialTensorTent k (constantRadialTensorTentBoundaryPoint k) = 1 := by
  let i : Fin (k + 2) := ⟨0, by omega⟩
  let j : Fin (k + 2) := ⟨0, by omega⟩
  simpa [constantRadialTensorTent, constantRadialTensorTentBoundaryPoint, i, j]
    using finiteRadialGridInterpolant_position
      (k + 2) (1 / (k + 2 : Real)) (by positivity)
      (fun _ _ : Fin (k + 2) ↦ (1 : Complex)) i j


theorem constantRadialTensorTent_cellPoint
    (k i j : Nat) (hi : i + 1 < k + 2) (hj : j + 1 < k + 2)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    constantRadialTensorTent k
      (isingRadialGridCellPoint (1 / (k + 2 : Real)) i j x y) = 1 := by
  rw [constantRadialTensorTent, finiteRadialGridInterpolant_cellPoint
    (1 / (k + 2 : Real)) (by positivity) _ i j hi hj x y hx0 hx1 hy0 hy1]
  simp [complexBilinearCell]
  ring

@[simp] theorem constantRadialTensorTent_exteriorPoint (k : Nat) :
    constantRadialTensorTent k (constantRadialTensorTentExteriorPoint k) = 0 := by
  classical
  unfold constantRadialTensorTent constantRadialTensorTentExteriorPoint
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_cellPoint (1 / (k + 2 : Real))
    (by positivity) 0 0 (-1) 0]
  apply Finset.sum_eq_zero
  intro i hi
  have hi0 : (0 : Real) ≤ i.1 := by positivity
  have htent : isingLinearTent ((-1 : Real) - (i.1 : Real)) = 0 := by
    unfold isingLinearTent
    rw [abs_of_nonpos (by linarith)]
    simp
  simp [htent]

theorem constantRadialTensorTent_points_tendsto_same :
    Tendsto (fun k ↦ dist (constantRadialTensorTentBoundaryPoint k)
      (constantRadialTensorTentExteriorPoint k)) atTop (nhds 0) := by
  have hmesh : Tendsto (fun k : Nat ↦ 1 / (k + 2 : Real)) atTop (nhds 0) := by
    convert ((tendsto_natCast_atTop_atTop (R := Real)).comp
      (Filter.tendsto_add_atTop_nat 2) |>.const_div_atTop 1) using 1 <;>
      simp [Function.comp_apply]
  have hboundary : Tendsto constantRadialTensorTentBoundaryPoint atTop (nhds 0) := by
    change Tendsto (fun k : Nat ↦
      isingRadialGridPosition (1 / (k + 2 : Real)) 0 0) atTop (nhds 0)
    simpa [isingRadialGridPosition, Nat.cast_add, Nat.cast_ofNat] using
      hmesh.ofReal.mul_const (⟨(1 : Real) / 2, 0⟩ : Complex)
  have hexterior : Tendsto constantRadialTensorTentExteriorPoint atTop (nhds 0) := by
    change Tendsto (fun k : Nat ↦
      isingRadialGridCellPoint (1 / (k + 2 : Real)) 0 0 (-1) 0)
        atTop (nhds 0)
    simpa [isingRadialGridCellPoint, Nat.cast_add, Nat.cast_ofNat] using
      hmesh.ofReal.mul_const (⟨0, (-1 : Real) / 2⟩ : Complex)
  simpa using hboundary.dist hexterior


theorem constantRadialTensorTent_not_meshUniformFullHolder :
    ¬ Nonempty
      (FKIsingCaratheodoryApproximation.MeshUniformFullHolder
        constantRadialTensorTent) := by
  rintro ⟨H⟩
  have hdistOut (k : Nat) :
      dist (constantRadialTensorTent k (constantRadialTensorTentBoundaryPoint k))
        (constantRadialTensorTent k (constantRadialTensorTentExteriorPoint k)) = 1 := by
    simp [dist_eq_norm]
  have hinput := constantRadialTensorTent_points_tendsto_same
  have halpha : (0 : Real) < (H.exponent : Real) := H.exponent_pos
  have hrpow : Tendsto (fun k ↦
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real))
      atTop (nhds 0) := by
    have ht := (Real.continuousAt_rpow_const 0 (H.exponent : Real)
      (Or.inr halpha.le)).tendsto.comp hinput
    simpa [Real.zero_rpow halpha.ne'] using ht
  have hrhs : Tendsto (fun k ↦ (H.constant : Real) *
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real))
      atTop (nhds 0) := by
    simpa using hrpow.const_mul (H.constant : Real)
  have hevent : ∀ᶠ k in atTop, (H.constant : Real) *
      dist (constantRadialTensorTentBoundaryPoint k)
        (constantRadialTensorTentExteriorPoint k) ^ (H.exponent : Real) < 1 :=
    (tendsto_order.1 hrhs).2 1 (by norm_num)
  rw [eventually_atTop] at hevent
  obtain ⟨k, hk⟩ := hevent
  have hk' := hk k (le_refl k)
  have hholder := (H.holder k).dist_le
    (constantRadialTensorTentBoundaryPoint k)
    (constantRadialTensorTentExteriorPoint k)
  rw [hdistOut k] at hholder
  exact (not_lt_of_ge hholder) hk'

end
end StatMech.Universality
