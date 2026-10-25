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
import Structure.v1.Atlas.Buildings.code.Building.BornologyGroups
set_option linter.unusedSectionVars false

open Set Filter Classical


namespace BornologicalGroupData

variable {G : Type*} [Group G]

/-- Underlying mathlib `Bornology` instance from `BornologicalGroupData`. -/
def toBornology (bd : BornologicalGroupData G) : Bornology G :=
  Bornology.ofBounded bd.bounded bd.empty_mem
    (fun s₁ hs₁ s₂ hs₂ => bd.subset_mem s₁ hs₁ s₂ hs₂)
    (fun s₁ hs₁ s₂ hs₂ => bd.union_mem s₁ hs₁ s₂ hs₂)
    bd.singleton_mem

end BornologicalGroupData

namespace BNPairBornology

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- $E \subseteq G$ is bounded relative to a BN-pair if it is covered by finitely many Bruhat cells. -/
def IsBounded (bp : BNPair G M) (E : Set G) : Prop :=
  ∃ (S : Finset M.Group), E ⊆ ⋃ w ∈ S, bp.bruhatCell w

/-- The collection of all sets bounded relative to a BN-pair. -/
def boundedSets (bp : BNPair G M) : Set (Set G) :=
  {E | IsBounded bp E}

end BNPairBornology
