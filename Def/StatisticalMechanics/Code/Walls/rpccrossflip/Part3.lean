/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part2
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def rpc_crossEdge (u v : Site 2) : Sym2 (Site 2) := by
  classical
  exact
    if v 0 = u 0 + 1 then rpc_hCrossEdge u
    else if u 0 = v 0 + 1 then rpc_hCrossEdge v
    else if v 1 = u 1 + 1 then rpc_vCrossEdge u
    else rpc_vCrossEdge v


end Walls
end StatMech
