/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldGhost
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent Lattice


def abbTarget (d n : Nat) : Set (Option (sctBox d n)) :=
  {z | z = none ∨ ∃ x : sctBox d n,
    z = some x ∧ (x : Site d) ∈ vertexBoundary d n}

end Sharpness
end StatMech
