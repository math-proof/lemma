/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEdges
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Def.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv
open scoped BigOperators Classical
open Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


@[simp] theorem restrictActive_extendActive (omega : ConfigSpace G.edgeSet) :
    restrictActive G (extendActive G omega) = omega := by
  funext e
  exact extendActive_apply G omega e


end FK
end StatMech
