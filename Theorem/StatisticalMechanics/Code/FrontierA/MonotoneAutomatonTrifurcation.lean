/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonTrifurcation


namespace StatMech.FrontierA

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.Percolation

open StatMech.Walls


variable {V : Type*} [Fintype V] [Nonempty V]


omit [Nonempty V] in
@[simp] theorem mem_forestBranchVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : v ∈ forestBranchVertices G ↔ 3 ≤ G.degree v := by
  simp [forestBranchVertices]

omit [Nonempty V] in
@[simp] theorem mem_forestLeaves (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : v ∈ forestLeaves G ↔ G.degree v = 1 := by
  simp [forestLeaves]


theorem finite_forest_branch_count_le_leaves (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (forestBranchVertices G).card ≤ (forestLeaves G).card := by
  simpa only [forestBranchVertices, forestLeaves] using
    bfk_forestHandshake G hacyclic hmin


theorem finite_forest_encounter_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (T B : Finset V) (hbranch : ∀ v ∈ T, 3 ≤ G.degree v)
    (hleaf : ∀ v, G.degree v = 1 → v ∈ B) :
    T.card ≤ B.card := by
  have hTB : T ⊆ forestBranchVertices G := by
    intro v hv
    exact mem_forestBranchVertices G v |>.mpr (hbranch v hv)
  have hLB : forestLeaves G ⊆ B := by
    intro v hv
    exact hleaf v (mem_forestLeaves G v |>.mp hv)
  calc
    T.card ≤ (forestBranchVertices G).card := Finset.card_le_card hTB
    _ ≤ (forestLeaves G).card :=
      finite_forest_branch_count_le_leaves G hacyclic hmin
    _ ≤ B.card := Finset.card_le_card hLB


variable {d : ℕ}


theorem deleteVertex_openSubgraph_eq_removeSite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bkg_deleteVertex (openSubgraph d omega) x = openSubgraph d (removeSite x omega) := by
  rw [oaf_openSubgraph_removeSite]
  rfl


theorem fineTrifurcation_of_canonical
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : IsCanonicalTrifurcation d omega x) : bft_FineTrif omega x := by
  obtain ⟨a1, a2, a3, _hne, ⟨ha1, ha2, ha3⟩,
    ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩ := h
  rw [bft_fineTrif_iff]
  refine ⟨a1, a2, a3, ⟨ha1, ha2, ha3⟩, ?_, ?_⟩
  · simpa only [daep_removeSites_singleton] using
      (show (cluster d (removeSite x omega) a1).Infinite ∧
          (cluster d (removeSite x omega) a2).Infinite ∧
          (cluster d (removeSite x omega) a3).Infinite from
        ⟨hinf1, hinf2, hinf3⟩)
  · have hcut := deleteVertex_openSubgraph_eq_removeSite omega x
    rw [hcut]
    exact ⟨hsep12, hsep13, hsep23⟩


end StatMech.FrontierA
