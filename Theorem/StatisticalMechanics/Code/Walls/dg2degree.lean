/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem dg2_degree_eq_transitions (K : Set (Site 2)) (a b : ℤ) :
    (faceBoundaryGraph K).degree ![a, b] = faceBoundaryDegree K a b :=
  degree_faceBoundaryGraph K a b


theorem dg2_bdInd_eq (K : Set (Site 2)) (x y : Site 2) :
    bdInd K x y = if (x ∈ K ↔ y ∉ K) then 1 else 0 := rfl


end Walls
end StatMech
