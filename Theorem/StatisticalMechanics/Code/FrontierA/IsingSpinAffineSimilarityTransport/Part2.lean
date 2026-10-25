/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinAffineSimilarityTransport
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


@[simp] theorem deriv_inverseUniformScaleAffineConformalMap
    (ρ : Real) (b z : Complex) :
    deriv (inverseUniformScaleAffineConformalMap ρ b) z = (ρ⁻¹ : Complex) := by
  have hderiv := (((hasDerivAt_id z).const_mul (ρ⁻¹ : Complex)).add_const b).deriv
  change deriv (fun y : Complex ↦ (ρ⁻¹ : Complex) * y + b) z =
    (ρ⁻¹ : Complex)
  simpa only [mul_one, add_zero, id_eq] using hderiv


theorem spinConformalFactor_inverseUniformScaleAffineConformalMap
    (ι : Type*) [Fintype ι] (a : ι → Complex) (b : Complex)
    {ρ : Real} (hρ : 0 < ρ) :
    spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a =
      ∏ _ : ι, ρ ^ (-isingSpinScalingDimension) := by
  classical
  unfold spinConformalFactor spinDerivativeFactor
  apply Finset.prod_congr rfl
  intro i _hi
  change ‖deriv (inverseUniformScaleAffineConformalMap ρ b) (a i)‖ ^
      isingSpinScalingDimension = ρ ^ (-isingSpinScalingDimension)
  rw [deriv_inverseUniformScaleAffineConformalMap,
    show (ρ⁻¹ : Complex) = (ρ : Complex)⁻¹ by norm_num,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
    Real.rpow_neg_eq_inv_rpow]


theorem tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel
    (ι : Type*) [Fintype ι]
    (reindex : Nat → Nat) (hreindex : Tendsto reindex atTop atTop)
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n,
      boxVerts 2 (sourceRadius (reindex n)) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius (reindex n))).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked (reindex n) i) = targetMarked n i)
    (a : ι → Complex) (b : Complex) {ρ L : Real} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n))
      atTop (nhds ρ))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds
        (spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a * L)) := by
  rw [spinConformalFactor_inverseUniformScaleAffineConformalMap ι a b hρ]
  exact tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel
    ι reindex hreindex sourceδ targetδ hsourceδ htargetδ β h
      sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked
      hρ hratio hsource


theorem tendsto_squareBoxRenormalizedSpinCorrelation_affine_reindex
    (ι : Type*) [Fintype ι]
    (reindex : Nat → Nat) (hreindex : Tendsto reindex atTop atTop)
    (sourceδ targetδ : Nat → Real)
    (hsourceδ : ∀ n, 0 < sourceδ n) (htargetδ : ∀ n, 0 < targetδ n)
    (β h : Real) (sourceRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (a : ι → Complex) (b : Complex) {ρ L : Real} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n))
      atTop (nhds ρ))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h (sourceRadius ∘ reindex)
          (fun n ↦ sourceMarked (reindex n)))
      atTop (nhds
        (spinConformalFactor (inverseUniformScaleAffineConformalMap ρ b) a * L)) := by
  exact tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel
    ι reindex hreindex sourceδ targetδ hsourceδ htargetδ β h
      sourceRadius (sourceRadius ∘ reindex) sourceMarked
      (fun n ↦ sourceMarked (reindex n))
      (fun _ ↦ Equiv.refl _)
      (fun _ _ _ ↦ Iff.rfl) (fun _ _ ↦ rfl)
      a b hρ hratio hsource

end StatMech.FrontierA
