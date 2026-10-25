/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part5


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp]
theorem numVertices_eq (w : HexWalk) : w.numVertices = w.turns.length + 1 := rfl

@[simp]
theorem length_vertices_eq_numVertices (w : HexWalk) :
    w.vertices.length = w.numVertices := by simp [numVertices]


end HexWalk
end StatMech.Universality
