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
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part3
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


theorem squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
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
    (hmarked : ∀ n i, σ n (sourceMarked n i) = targetMarked n i) (n : Nat) :
    squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked n =
      (∏ _ : ι,
          (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension)) *
        squareBoxRenormalizedSpinCorrelation
          ι sourceδ β h sourceRadius sourceMarked n := by
  unfold squareBoxRenormalizedSpinCorrelation spinRenormalizedCorrelation
  have hraw := congrFun (squareBoxMovingSpinCorrelation_eq_of_relabel
    ι β h sourceRadius targetRadius sourceMarked targetMarked σ hσ hmarked) n
  rw [← hraw, spinMeshRenormalization_uniformScale
    ι (hsourceδ n) (htargetδ n)]
  ring


theorem tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
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
    {ρ L : Real} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ n) atTop (nhds ρ))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds ((∏ _ : ι, ρ ^ (-isingSpinScalingDimension)) * L)) := by
  have hratioPow : Tendsto
      (fun n ↦ (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension))
      atTop (nhds (ρ ^ (-isingSpinScalingDimension))) :=
    hratio.rpow_const (Or.inl hρ.ne')
  have hfactor : Tendsto
      (fun n ↦ ∏ _ : ι,
        (targetδ n / sourceδ n) ^ (-isingSpinScalingDimension))
      atTop (nhds (∏ _ : ι, ρ ^ (-isingSpinScalingDimension))) := by
    exact tendsto_finsetProd Finset.univ (fun _ _ ↦ hratioPow)
  refine (hfactor.mul hsource).congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  exact (squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    ι sourceδ targetδ hsourceδ htargetδ β h sourceRadius targetRadius
    sourceMarked targetMarked σ hσ hmarked n).symm


end StatMech.FrontierA
