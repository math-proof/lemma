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
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part2
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


theorem squareBoxMovingSpinCorrelation_nonneg
    (ι : Type*) [Fintype ι]
    (β h : Real) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (radius : Nat → Nat)
    (marked : ∀ n, ι ↪ boxVerts 2 (radius n)) (n : Nat) :
    0 ≤ squareBoxMovingSpinCorrelation ι β h radius marked n := by
  exact finiteMarkedSpinCorrelation_nonneg
    (boxGraph 2 (radius n)) β h hβ hh (marked n)


theorem squareBoxMovingSpinCorrelation_eq_of_relabel
    (ι : Type*) [Fintype ι]
    (β h : Real) (sourceRadius targetRadius : Nat → Nat)
    (sourceMarked : ∀ n, ι ↪ boxVerts 2 (sourceRadius n))
    (targetMarked : ∀ n, ι ↪ boxVerts 2 (targetRadius n))
    (σ : ∀ n, boxVerts 2 (sourceRadius n) ≃ boxVerts 2 (targetRadius n))
    (hσ : ∀ n x y,
      (boxGraph 2 (sourceRadius n)).Adj x y ↔
        (boxGraph 2 (targetRadius n)).Adj (σ n x) (σ n y))
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) :
    squareBoxMovingSpinCorrelation ι β h sourceRadius sourceMarked =
      squareBoxMovingSpinCorrelation ι β h targetRadius targetMarked := by
  funext n
  rw [squareBoxMovingSpinCorrelation, squareBoxMovingSpinCorrelation]
  have htransport := finiteMarkedSpinCorrelation_relabel
    (boxGraph 2 (sourceRadius n)) (boxGraph 2 (targetRadius n))
    (σ n) (hσ n) β h (sourceMarked n)
  have hmarkedEmbedding :
      (sourceMarked n).trans (σ n).toEmbedding = targetMarked n := by
    apply DFunLike.ext _ _
    intro i
    exact hmarked n i
  simpa only [hmarkedEmbedding] using htransport


theorem spinMeshRenormalization_uniformScale
    (ι : Type*) [Fintype ι] {sourceδ targetδ : Real}
    (hsourceδ : 0 < sourceδ) (htargetδ : 0 < targetδ) :
    spinMeshRenormalization ι targetδ =
      (∏ _ : ι, (targetδ / sourceδ) ^ (-isingSpinScalingDimension)) *
        spinMeshRenormalization ι sourceδ := by
  unfold spinMeshRenormalization
  rw [Finset.prod_const, Finset.card_univ]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg htargetδ.le hsourceδ.le)]
  rw [show -isingSpinScalingDimension * (Fintype.card ι : Real) =
    -(Fintype.card ι : Real) * isingSpinScalingDimension by ring]
  rw [← Real.mul_rpow (div_nonneg htargetδ.le hsourceδ.le) hsourceδ.le]
  congr 1
  field_simp


end StatMech.FrontierA
