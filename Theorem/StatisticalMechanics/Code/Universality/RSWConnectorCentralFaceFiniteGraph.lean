/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorCentralFaceFiniteGraph_le_closureGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤
      rlc_connectorCentralFaceClosureGraph gamma gamma' := by
  rintro x y ⟨hxy, he⟩
  exact ⟨hxy, Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1⟩


end
end StatMech.Universality
