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
import Structure.v1.Atlas.Buildings.code.Building.CompactSubgroups
set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace CompactSubgroups

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A subgroup $H$ is bounded in the bornology $\mathrm{born}$ if its underlying set is bounded. -/
def IsBoundedSubgroup (born : GroupBornology G) (H : Subgroup G) : Prop :=
  born.isBounded (H : Set G)

/-- A subgroup $K$ is *maximal bounded* if it is bounded and no strictly larger subgroup is bounded. -/
def IsMaximalBounded (born : GroupBornology G) (K : Subgroup G) : Prop :=
  IsBoundedSubgroup born K ∧ ∀ H : Subgroup G, K < H → ¬IsBoundedSubgroup born H

/-- $S$ is BN-pair bounded: covered by finitely many Bruhat cells of $\mathrm{bp}$. -/
def BNPairBoundedPredicate (bp : BNPair G M) (S : Set G) : Prop :=
  ∃ (ws : Finset M.Group), S ⊆ ⋃ w ∈ ws, bp.bruhatCell w

end CompactSubgroups
