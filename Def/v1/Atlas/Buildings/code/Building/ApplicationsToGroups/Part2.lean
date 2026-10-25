/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.OpenSubgroup
import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part2
set_option linter.unusedSectionVars false

open ChamberComplex


section Parahorics

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- The parahoric/parabolic correspondence asserts that for every subset
$J \subseteq B$ there is a (typically smaller) subset $J_0 \subseteq J$ with
$P_J \subseteq P_{J_0}$. -/
def ParahoricParabolicCorrespondence {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) : Prop :=
  ∀ (J : Set B_idx),
    ∃ (J₀ : Set B_idx), J₀ ⊆ J ∧

      bp.standardParabolic J ⊆ bp.standardParabolic J₀

end Parahorics

section Decompositions

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- The Bruhat decomposition predicate on a BN-pair: $G$ is the disjoint union
of the Bruhat cells $BwB$ indexed by $w \in W$. -/
def BruhatDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) : Prop :=

  (∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w) ∧

  (∀ w₁ w₂ : M.Group, w₁ ≠ w₂ →
    Disjoint (bp.bruhatCell w₁) (bp.bruhatCell w₂))

/-- The Cartan decomposition $G = KAK$: every $g \in G$ factors as $g = k_1 a k_2$
with $k_1, k_2 \in K$ and $a \in A$, where $K$ is a maximal compact subgroup
and $A$ is a chosen torus or split component. -/
def CartanDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (_bp : BNPair G M) (K : Subgroup G) (A : Set G) : Prop :=

  ∀ g : G, ∃ (k₁ : K) (a : G) (k₂ : K),
    a ∈ A ∧ g = k₁ * a * k₂

/-- The Iwasawa decomposition $G = KAN$: every $g \in G$ factors as $g = kan$ with
$k \in K$, $a \in A$ and $n \in N$ unipotent. -/
def IwasawaDecomposition {G : Type*} [Group G]
    {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (_bp : BNPair G M) (K : Subgroup G)
    (A : Set G) (N_unip : Set G) : Prop :=

  ∀ g : G, ∃ (k : K) (a : G) (n : G),
    a ∈ A ∧ n ∈ N_unip ∧ g = k * a * n

end Decompositions
