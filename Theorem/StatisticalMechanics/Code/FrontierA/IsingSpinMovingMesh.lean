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
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


theorem finiteMarkedSpinCorrelation_nonneg
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β h : Real) (hβ : 0 ≤ β) (hh : 0 ≤ h) (marked : ι ↪ V) :
    0 ≤ finiteMarkedSpinCorrelation G β h marked := by
  exact gks_first G β h hβ hh (Finset.univ.map marked)


theorem finiteMarkedSpinCorrelation_relabel
    {V W ι : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (σ : V ≃ W)
    (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
    (β h : Real) (marked : ι ↪ V) :
    finiteMarkedSpinCorrelation G β h marked =
      finiteMarkedSpinCorrelation H β h
        (marked.trans σ.toEmbedding) := by
  unfold finiteMarkedSpinCorrelation
  rw [isingExpectation_spinProd_relabel G H σ hσ]
  congr 2
  ext y
  simp only [Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coe_trans, Equiv.coe_toEmbedding, Function.comp_apply]
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, hv⟩
    exact ⟨i, hv⟩
  · rintro ⟨i, hi⟩
    exact ⟨marked i, ⟨i, rfl⟩, hi⟩


end StatMech.FrontierA
