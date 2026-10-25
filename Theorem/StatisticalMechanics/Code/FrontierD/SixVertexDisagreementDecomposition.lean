/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (v : T.Vertex) (d : Fin 4) :
    sixVertexLocalIncomingPattern omega v d ≠
        sixVertexLocalIncomingPattern eta v d ↔
      sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusIncidentEdge T v d) := by
  fin_cases d <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusIncidentEdge,
      sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming]


end
end StatMech.FrontierD
