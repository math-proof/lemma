/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinAffineSimilarityTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


theorem squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel
    (ι : Type*) [Fintype ι]
    (reindex : Nat → Nat)
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
    (n : Nat) :
    squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked n =
      (∏ _ : ι,
          (targetδ n / sourceδ (reindex n)) ^ (-isingSpinScalingDimension)) *
        squareBoxRenormalizedSpinCorrelation
          ι sourceδ β h sourceRadius sourceMarked (reindex n) := by
  simpa only [Function.comp_apply] using
    (squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
      ι (sourceδ ∘ reindex) targetδ
      (fun n ↦ hsourceδ (reindex n)) htargetδ β h
      (sourceRadius ∘ reindex) targetRadius
      (fun n ↦ sourceMarked (reindex n)) targetMarked σ hσ hmarked n)


theorem tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel
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
    {ρ L : Real} (hρ : 0 < ρ)
    (hratio : Tendsto (fun n ↦ targetδ n / sourceδ (reindex n))
      atTop (nhds ρ))
    (hsource : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked)
      atTop (nhds L)) :
    Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι targetδ β h targetRadius targetMarked)
      atTop (nhds ((∏ _ : ι, ρ ^ (-isingSpinScalingDimension)) * L)) := by
  have hsourceAligned : Tendsto
      (squareBoxRenormalizedSpinCorrelation
        ι (sourceδ ∘ reindex) β h (sourceRadius ∘ reindex)
          (fun n ↦ sourceMarked (reindex n)))
      atTop (nhds L) := by
    change Tendsto (fun n ↦
      squareBoxRenormalizedSpinCorrelation
        ι sourceδ β h sourceRadius sourceMarked (reindex n))
      atTop (nhds L)
    exact hsource.comp hreindex
  exact tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_relabel
    ι (sourceδ ∘ reindex) targetδ
      (fun n ↦ hsourceδ (reindex n)) htargetδ β h
      (sourceRadius ∘ reindex) targetRadius
      (fun n ↦ sourceMarked (reindex n)) targetMarked σ hσ hmarked
      hρ hratio hsourceAligned


end StatMech.FrontierA
