/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part5
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrActiveGhost (o : V)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    Finset {e // e ∈ FieldGhostDict.ghostEdges V} :=
  (abgrActive (G := G) o
    (abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta)).map
      (abgrGhostEdgeEquiv (V := V)).toEmbedding

end Sharpness
end StatMech
