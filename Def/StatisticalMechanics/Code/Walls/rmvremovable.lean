/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
import Theorem.StatisticalMechanics.Code.Walls.rmvremovable
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


noncomputable def rmv_block : Set (Site 2) := {![0, 0], ![1, 0], ![0, 1], ![1, 1]}

end Walls
end StatMech
