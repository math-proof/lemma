/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgeexploration.Part2
import Instance.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bct_dstarG_isTree : bct_dstarG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨by rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩,
    by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide⟩


theorem bct_dstarG_isAcyclic : bct_dstarG.IsAcyclic := bct_dstarG_isTree.isAcyclic


theorem bct_dstarG_hub0_deg : bct_dstarG.degree 0 = 3 := by decide


theorem bct_dstarG_hub1_deg : bct_dstarG.degree 1 = 3 := by decide


theorem bct_dstarG_leaf_deg : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → bct_dstarG.degree i = 1 := by decide


theorem bct_dstarG_min_deg : ∀ i : Fin 6, 1 ≤ bct_dstarG.degree i := by decide


theorem bct_dstarG_deg1_iff (i : Fin 6) : bct_dstarG.degree i = 1 ↔ (i ≠ 0 ∧ i ≠ 1) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro rfl; rw [bct_dstarG_hub0_deg] at h; exact absurd h (by decide)
    · rintro rfl; rw [bct_dstarG_hub1_deg] at h; exact absurd h (by decide)
  · exact fun ⟨h0, h1⟩ => bct_dstarG_leaf_deg i h0 h1


theorem bct_exploration_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic)
    (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    bfg_GenuineExploration ω L R :=
  ⟨W, inferInstance, inferInstance, inferInstance, G, inferInstance, ιT, comp,
    hacyc, hmin, hdeg3, hinj, hbnd, hdisj⟩


open Classical in


theorem bct_exploration_of_twoSharedTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (hy0 : btr_IsGenuineCoarseTrif ω L y₀) (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
    (hy0box : y₀ ∈ box d R) (hy1box : y₁ ∈ box d R) (hne : y₀ ≠ y₁)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
    (comp : Fin 6 → Set (Site d))
    (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j →
      Disjoint (comp i) (comp j)) :
    bfg_GenuineExploration ω L R := by
  classical
  
  let ιT : Site d → Fin 6 := fun z => if z = y₀ then 0 else if z = y₁ then 1 else 0
  have hιT0 : ιT y₀ = 0 := by simp [ιT]
  have hιT1 : ιT y₁ = 1 := by simp [ιT, (Ne.symm hne)]
  refine bct_exploration_of_carrier ω L R (Fin 6) bct_dstarG ιT comp
    bct_dstarG_isAcyclic bct_dstarG_min_deg ?_ ?_ ?_ ?_
  · 
    intro z hzbox hzgen
    rcases huniq z hzbox hzgen with rfl | rfl
    · rw [hιT0, bct_dstarG_hub0_deg]
    · rw [hιT1, bct_dstarG_hub1_deg]
  · 
    intro z hzbox hzgen z' hz'box hz'gen hzz
    rcases huniq z hzbox hzgen with rfl | rfl <;>
      rcases huniq z' hz'box hz'gen with rfl | rfl
    · rfl
    · rw [hιT0, hιT1] at hzz; exact absurd hzz (by decide)
    · rw [hιT0, hιT1] at hzz; exact absurd hzz.symm (by decide)
    · rfl
  · 
    intro v hv
    rw [bct_dstarG_deg1_iff] at hv
    exact hcompB v hv.1 hv.2
  · 
    intro u hu v hv huv
    rw [bct_dstarG_deg1_iff] at hu hv
    exact hcompD u hu.1 hu.2 v hv.1 hv.2 huv


theorem bct_genuineForest_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    bgt_GenuineForest ω L R :=
  bfg_genuineForest_of_exploration ω L R
    (bct_exploration_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj)


theorem bct_genuineTcount_of_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (ιT : Site d → W) (comp : W → Set (Site d))
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y))
    (hinj : ∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z)
    (hbnd : ∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bgt_genuineTcount_le_boundary ω L R
    (bct_genuineForest_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj)


theorem bct_twoSharedTrif_genuineForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {y₀ y₁ : Site d} (hy0 : btr_IsGenuineCoarseTrif ω L y₀) (hy1 : btr_IsGenuineCoarseTrif ω L y₁)
    (hy0box : y₀ ∈ box d R) (hy1box : y₁ ∈ box d R) (hne : y₀ ≠ y₁)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y₀ ∨ z = y₁)
    (comp : Fin 6 → Set (Site d))
    (hcompB : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → (comp i ∩ vertexBoundary d R).Nonempty)
    (hcompD : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → ∀ j : Fin 6, j ≠ 0 → j ≠ 1 → i ≠ j →
      Disjoint (comp i) (comp j)) :
    bgt_GenuineForest ω L R :=
  bfg_genuineForest_of_exploration ω L R
    (bct_exploration_of_twoSharedTrif ω L R hy0 hy1 hy0box hy1box hne huniq comp hcompB hcompD)


theorem bct_genuineTcount_of_connectedTree (L R : ℕ)
    (hexpl : ∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)),
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  fun ω => bfg_genuineTcount_le_boundary ω L R (hexpl ω)


theorem bct_status :
    
    (∀ (β V : Type) (H : SimpleGraph V), H.IsAcyclic → (bct_fiberForest β V H).IsAcyclic) ∧
    
    bct_dstarG.IsTree ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (W : Type) [Fintype W] [Nonempty W]
      [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
      (ιT : Site d → W) (comp : W → Set (Site d)),
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y)) →
      (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
        btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z) →
      (∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty) →
      (∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v)) →
      bfg_GenuineExploration ω L R) ∧
    
    (∀ (L R : ℕ), (∀ ω : ConfigSpace (Sym2 (Site d)), bfg_GenuineExploration ω L R) →
      ∀ ω : ConfigSpace (Sym2 (Site d)),
        (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) := by
  refine ⟨fun β V H hH => bct_fiberForest_acyclic β V H hH, bct_dstarG_isTree, ?_, ?_⟩
  · intro ω L R W _ _ _ G _ ιT comp hacyc hmin hdeg3 hinj hbnd hdisj
    exact bct_exploration_of_carrier ω L R W G ιT comp hacyc hmin hdeg3 hinj hbnd hdisj
  · intro L R hexpl ω
    exact bct_genuineTcount_of_connectedTree L R hexpl ω

end StatMech.Walls
