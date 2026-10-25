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
import Def.v1.Atlas.Buildings.code.Building.BornologyGroups
set_option linter.unusedSectionVars false

open Set Filter Classical


/-- Data of a bornology compatible with the group structure on $G$: a family of bounded sets
closed under singletons, subsets, finite unions, group products, and inversion. -/
structure BornologicalGroupData (G : Type*) [Group G] where
  bounded : Set (Set G)
  singleton_mem : ∀ x : G, {x} ∈ bounded
  subset_mem : ∀ E ∈ bounded, ∀ F ⊆ E, F ∈ bounded
  union_mem : ∀ E ∈ bounded, ∀ F ∈ bounded, E ∪ F ∈ bounded
  mul_mem : ∀ E ∈ bounded, ∀ F ∈ bounded, GroupSetMul E F ∈ bounded
  inv_mem : ∀ E ∈ bounded, GroupSetInv E ∈ bounded

