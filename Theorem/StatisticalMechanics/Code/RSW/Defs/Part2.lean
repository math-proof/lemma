/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs.Part2
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp] theorem mem_leftSide {a b c d : ℤ} {x : Site 2} :
    x ∈ leftSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = a := Iff.rfl

@[simp] theorem mem_rightSide {a b c d : ℤ} {x : Site 2} :
    x ∈ rightSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = b := Iff.rfl

@[simp] theorem mem_bottomSide {a b c d : ℤ} {x : Site 2} :
    x ∈ bottomSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = c := Iff.rfl

@[simp] theorem mem_topSide {a b c d : ℤ} {x : Site 2} :
    x ∈ topSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = d := Iff.rfl

theorem leftSide_subset {a b c d : ℤ} : leftSide a b c d ⊆ rect a b c d := fun _ hx => hx.1

theorem rightSide_subset {a b c d : ℤ} : rightSide a b c d ⊆ rect a b c d := fun _ hx => hx.1

theorem bottomSide_subset {a b c d : ℤ} : bottomSide a b c d ⊆ rect a b c d := fun _ hx => hx.1

theorem topSide_subset {a b c d : ℤ} : topSide a b c d ⊆ rect a b c d := fun _ hx => hx.1


end Box
end RSW
end StatMech
