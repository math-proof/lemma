/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pcffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Walls.pcffaceclose
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


@[simp] theorem pcf_faceCutGraph_adj (T : Site 2 → Prop) (f g : Site 2) :
    (pcf_faceCutGraph T).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ (T f ↔ ¬ T g) := Iff.rfl


theorem pcf_faceCutGraph_le (T : Site 2 → Prop) :
    pcf_faceCutGraph T ≤ hypercubicLattice 2 := fun _ _ h => h.1


end Walls
end StatMech
