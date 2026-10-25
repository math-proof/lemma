/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups.Part2
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 800000


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Data underlying an affine Weyl group: a reduced root system $Φ$ in $E$, the linear
Weyl subgroup, and a coroot lattice stable under the Weyl group. -/
structure AffineWeylGroupData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  roots : Set E
  roots_ne_zero : ∀ α ∈ roots, α ≠ 0
  roots_reduced : ∀ α ∈ roots, ∀ t : ℝ, t • α ∈ roots → t = 1 ∨ t = -1
  weylGroup : Subgroup (E ≃ₗᵢ[ℝ] E)
  corootLattice : AddSubgroup E
  weylGroup_stable_corootLattice :
    ∀ w ∈ weylGroup, ∀ v ∈ corootLattice, w v ∈ corootLattice

end
