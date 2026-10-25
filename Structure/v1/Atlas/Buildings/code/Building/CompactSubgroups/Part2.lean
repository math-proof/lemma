/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CompactSubgroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Def.v1.Atlas.Buildings.code.Building.CompactSubgroups
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace CompactSubgroups

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

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

end CompactSubgroups
