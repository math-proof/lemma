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
import Theorem.StatisticalMechanics.Code.Walls.dg2degree.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


def dg2_pinchSet : Set (Site 2) := {![(0:ℤ), 0], ![(1:ℤ), 1]}


end Walls
end StatMech
