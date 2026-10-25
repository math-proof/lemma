/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinMovingMesh.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


@[simp] theorem deriv_inverseUniformScaleConformalMap
    (rho : Real) (z : Complex) :
    deriv (inverseUniformScaleConformalMap rho) z = (rho⁻¹ : Complex) := by
  have h := ((hasDerivAt_id z).const_mul (rho⁻¹ : Complex)).deriv
  change deriv (fun y : Complex ↦ (rho⁻¹ : Complex) * y) z =
    (rho⁻¹ : Complex)
  simpa only [mul_one, id_eq] using h


theorem spinConformalFactor_inverseUniformScaleConformalMap
    (ι : Type*) [Fintype ι] (a : ι → Complex)
    {rho : Real} (hrho : 0 < rho) :
    spinConformalFactor (inverseUniformScaleConformalMap rho) a =
      ∏ _ : ι, rho ^ (-isingSpinScalingDimension) := by
  classical
  unfold spinConformalFactor spinDerivativeFactor
  apply Finset.prod_congr rfl
  intro i _hi
  change ‖deriv (inverseUniformScaleConformalMap rho) (a i)‖ ^
      isingSpinScalingDimension = rho ^ (-isingSpinScalingDimension)
  rw [deriv_inverseUniformScaleConformalMap,
    show (rho⁻¹ : Complex) = (rho : Complex)⁻¹ by norm_num,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrho,
    Real.rpow_neg_eq_inv_rpow]


theorem tendsto_squareBoxRenormalizedSpinCorrelation_inverseUniformScale_of_relabel
    (ι : Type*) [Fintype ι]
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i)
    (a : ι → Complex) {rho L : Real} (hrho : 0 < rho)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n)
      atTop (nhds rho))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds
        (spinConformalFactor (inverseUniformScaleConformalMap rho) a * L)) := by
  rw [spinConformalFactor_inverseUniformScaleConformalMap ι a hrho]
  exact tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius
      sourceMarked targetMarked σ hσ hmarked hrho hratio hsource


theorem squareBox_radius_eq_of_equiv {sourceRadius targetRadius : Nat}
    (σ : boxVerts 2 sourceRadius ≃ boxVerts 2 targetRadius) :
    sourceRadius = targetRadius := by
  have hcard := Fintype.card_congr σ
  rw [ecz_boxVerts_card, ecz_boxVerts_card] at hcard
  have hside : 2 * sourceRadius + 1 = 2 * targetRadius + 1 :=
    Nat.pow_left_injective (by norm_num : (2 : Nat) ≠ 0) hcard
  omega


theorem squareBox_radiusSequence_eq_of_equiv
    {sourceRadius targetRadius : Nat → Nat}
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n)) :
    sourceRadius = targetRadius := by
  funext n
  exact squareBox_radius_eq_of_equiv (σ n)


theorem squareBoxRenormalizedSpinCorrelation_eq_of_relabel
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real)
    (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
    squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked =
      squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked := by
  unfold squareBoxRenormalizedSpinCorrelation
  rw [squareBoxMovingSpinCorrelation_eq_of_relabel
    ι β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked]


theorem squareBoxRenormalizedSpinCorrelation_transportError_eq_zero
    (ι : Type*) [Fintype ι]
    (δ : Nat → Real) (β h : Real)
    (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) (n : Nat) :
    squareBoxRenormalizedSpinCorrelation ι δ β h targetRadius targetMarked n -
      squareBoxRenormalizedSpinCorrelation ι δ β h sourceRadius sourceMarked n = 0 := by
  rw [squareBoxRenormalizedSpinCorrelation_eq_of_relabel
    ι δ β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked]
  exact sub_self _

end StatMech.FrontierA
