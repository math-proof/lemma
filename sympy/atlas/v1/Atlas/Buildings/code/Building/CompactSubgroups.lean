/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CompactSubgroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Affine
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ParabolicDefs
import Lemma.Nat.NonemptyBruhatCell

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace CompactSubgroups

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A bornology on a group $G$: a family of bounded sets closed under taking subsets, finite
unions, singletons, group products, and inversion. -/
structure GroupBornology (G : Type*) [Group G] where
  isBounded : Set G → Prop
  subset_bounded : ∀ {S T : Set G}, isBounded T → S ⊆ T → isBounded S
  singleton_bounded : ∀ (g : G), isBounded {g}
  union_bounded : ∀ {S T : Set G}, isBounded S → isBounded T → isBounded (S ∪ T)
  product_bounded : ∀ {S T : Set G}, isBounded S → isBounded T →
    isBounded (setMul S T)
  inv_bounded : ∀ {S : Set G}, isBounded S →
    isBounded ((fun x => x⁻¹) '' S)

/-- A subgroup $H$ is bounded in the bornology $\mathrm{born}$ if its underlying set is bounded. -/
def IsBoundedSubgroup (born : GroupBornology G) (H : Subgroup G) : Prop :=
  born.isBounded (H : Set G)

/-- A subgroup $K$ is *maximal bounded* if it is bounded and no strictly larger subgroup is bounded. -/
def IsMaximalBounded (born : GroupBornology G) (K : Subgroup G) : Prop :=
  IsBoundedSubgroup born K ∧ ∀ H : Subgroup G, K < H → ¬IsBoundedSubgroup born H

/-- $S$ is BN-pair bounded: covered by finitely many Bruhat cells of $\mathrm{bp}$. -/
def BNPairBoundedPredicate (bp : BNPair G M) (S : Set G) : Prop :=
  ∃ (ws : Finset M.Group), S ⊆ ⋃ w ∈ ws, bp.bruhatCell w

/-- Alias: every bounded subgroup is conjugate-contained in a vertex-stabilizer parabolic. -/
structure IsSpecialVertex (M : CoxeterMatrix B_idx)
    (linearPart : M.Group →* M.Group) (s₀ : B_idx) : Prop where
  surjective : ∀ wbar : M.Group, wbar ∈ Set.range linearPart →
    ∃ w : M.Group,
      w ∈ (Subgroup.closure
        (M.toCoxeterSystem.simple '' (Set.univ \ {s₀})) : Set M.Group) ∧
      linearPart w = wbar

/-- A *good maximal bounded subgroup*: a maximal bounded subgroup $K$ containing $B$ that equals
a coatom standard parabolic $P_{\mathrm{Univ} \setminus \{\mathrm{vertex}\}}$ where the vertex is special. -/
structure GoodMaximalBounded (bp : BNPair G M) (born : GroupBornology G)
    (linearPart : M.Group →* M.Group) where
  K : Subgroup G
  maximal_bounded : IsMaximalBounded born K
  contains_B : bp.B ≤ K
  vertex : B_idx
  eq_parabolic : (K : Set G) = bp.standardParabolic (Set.univ \ {vertex})
  is_special : IsSpecialVertex M linearPart vertex
