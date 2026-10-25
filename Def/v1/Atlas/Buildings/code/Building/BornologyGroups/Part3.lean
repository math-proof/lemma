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
import Theorem.v1.Atlas.Buildings.code.Building.BornologyGroups
set_option linter.unusedSectionVars false

open Set Filter Classical


namespace BNPairBornology

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- Promote a BN-pair with cover, product-closure, and inverse-closure to a `BornologicalGroupData`. -/
def toBornologicalGroupData (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w)
    (hmul : ∀ E ∈ boundedSets bp, ∀ F ∈ boundedSets bp,
      GroupSetMul E F ∈ boundedSets bp)
    (hinv : ∀ E ∈ boundedSets bp, GroupSetInv E ∈ boundedSets bp) :
    BornologicalGroupData G where
  bounded := boundedSets bp
  singleton_mem := singleton_isBounded bp hcover
  subset_mem := fun E hE F hFE => isBounded_subset bp hE hFE
  union_mem := fun E hE F hF => isBounded_union bp hE hF
  mul_mem := hmul
  inv_mem := hinv

/-- Bornology on $G$ induced by a BN-pair, given a Bruhat cover. -/
def toBornology (bp : BNPair G M)
    (hcover : ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) :
    Bornology G :=
  Bornology.ofBounded (boundedSets bp)
    (empty_isBounded bp)
    (fun E hE F hFE => isBounded_subset bp hE hFE)
    (fun E hE F hF => isBounded_union bp hE hF)
    (singleton_isBounded bp hcover)

/-- Generalized BN-pair boundedness using extended cells parameterized by $\Omega \times M.\mathrm{Group}$. -/
def IsBoundedGeneralized {Ω : Type*} (bp : BNPair G M)
    (extendedCells : Ω × M.Group → Set G) (E : Set G) : Prop :=
  ∃ (S : Finset (Ω × M.Group)), E ⊆ ⋃ σw ∈ S, extendedCells σw

end BNPairBornology
