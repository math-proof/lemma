/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/BornologyGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part4
import Lemma.Nat.TopologicalGroupDef
import Mathlib.Topology.Bornology.Basic
import Def.v1.Atlas.Buildings.code.Building.BornologyGroups.Part2
set_option linter.unusedSectionVars false

open Set Filter Classical


namespace BNPairBornology

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- Each Bruhat cell is bounded. -/
theorem bruhatCell_isBounded (bp : BNPair G M) (w : M.Group) :
    IsBounded bp (bp.bruhatCell w) :=
  ⟨{w}, subset_biUnion_of_mem (Finset.mem_singleton.mpr rfl)⟩

/-- BN-pair boundedness is closed under taking subsets. -/
theorem isBounded_subset (bp : BNPair G M) {E F : Set G}
    (hE : IsBounded bp E) (hFE : F ⊆ E) : IsBounded bp F := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, hFE.trans hS⟩

/-- BN-pair boundedness is closed under binary unions. -/
theorem isBounded_union (bp : BNPair G M) {E F : Set G}
    (hE : IsBounded bp E) (hF : IsBounded bp F) :
    IsBounded bp (E ∪ F) := by
  obtain ⟨S₁, hS₁⟩ := hE
  obtain ⟨S₂, hS₂⟩ := hF
  refine ⟨S₁ ∪ S₂, union_subset ?_ ?_⟩
  · exact hS₁.trans (biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_left))
  · exact hS₂.trans (biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_right))

/-- Singletons are bounded when the BN-pair Bruhat decomposition covers $G$. -/
theorem singleton_isBounded (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w)
    (g : G) : IsBounded bp {g} := by
  obtain ⟨w, hw⟩ := hcover g
  exact isBounded_subset bp (bruhatCell_isBounded bp w) (singleton_subset_iff.mpr hw)

/-- The empty set is BN-pair bounded. -/
theorem empty_isBounded (bp : BNPair G M) : IsBounded bp ∅ :=
  ⟨∅, empty_subset _⟩

end BNPairBornology
