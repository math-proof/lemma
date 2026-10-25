/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusEdgeArrow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Bool :=
  if e.1 = 0 then omega.horizontal e.2 else omega.vertical e.2

def sixVertexTorusEdgeDisagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Prop :=
  sixVertexTorusEdgeArrow omega e ≠ sixVertexTorusEdgeArrow eta e


def sixVertexTorusIncidentEdge
    (T : EvenTorus) (v : T.Vertex) (d : Fin 4) : SixVertexTorusEdge T :=
  ![(0, (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)),
    (0, v),
    (1, (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)),
    (1, v)] d

end
end StatMech.FrontierD
