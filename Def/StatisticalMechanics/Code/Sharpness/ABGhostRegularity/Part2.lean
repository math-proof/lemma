/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part2
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrKeepGhost (x : V) (omega : ConfigSpace (Sym2 (Option V))) :
    ConfigSpace (Sym2 (Option V)) := fun e =>
  if e = s(some x, none) then omega e
  else if e ∈ FieldGhostDict.ghostEdges V then false else omega e


noncomputable def abgrCloseGhost (omega : ConfigSpace (Sym2 (Option V))) :
    ConfigSpace (Sym2 (Option V)) := fun e =>
  if e ∈ FieldGhostDict.ghostEdges V then false else omega e

end Sharpness
end StatMech
