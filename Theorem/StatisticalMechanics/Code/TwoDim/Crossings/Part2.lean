/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.TwoDim.Crossings.Part2
open Set


namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


@[simp] theorem mem_leftSide {x : Site 2} :
    x ∈ leftSide a b ↔ x ∈ rectangle a b ∧ x 0 = 0 := Iff.rfl

@[simp] theorem mem_rightSide {x : Site 2} :
    x ∈ rightSide a b ↔ x ∈ rectangle a b ∧ x 0 = a := Iff.rfl

@[simp] theorem mem_bottomSide {x : Site 2} :
    x ∈ bottomSide a b ↔ x ∈ rectangle a b ∧ x 1 = 0 := Iff.rfl

@[simp] theorem mem_topSide {x : Site 2} :
    x ∈ topSide a b ↔ x ∈ rectangle a b ∧ x 1 = b := Iff.rfl

theorem leftSide_subset : leftSide a b ⊆ rectangle a b := fun _ hx => hx.1

theorem rightSide_subset : rightSide a b ⊆ rectangle a b := fun _ hx => hx.1

theorem bottomSide_subset : bottomSide a b ⊆ rectangle a b := fun _ hx => hx.1

theorem topSide_subset : topSide a b ⊆ rectangle a b := fun _ hx => hx.1


end TwoDim
end StatMech
