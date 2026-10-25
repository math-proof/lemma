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

end CompactSubgroups
