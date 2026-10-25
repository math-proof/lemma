/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorCentralFaceEdgeLift_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : Sym2 (Site 2))
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    (rlc_connectorCentralFaceEdgeLift e he).map Subtype.val = e :=
  Classical.choose_spec (centralFaceEdge_exists_lift he)


end
end StatMech.Universality
