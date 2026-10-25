/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part8
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectMedialDartAbovePrimalVertex
    (R : FKRectTorus) (x : R.Vertex) : FKMedialDart R.medialTorus :=
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  let e : R.EdgeIndex := (true, y)
  if Even y.2.val then
    fkMedialEastDart (fkRectMedialVertexOfEdge R e)
  else
    fkMedialWestDart (fkRectMedialVertexOfEdge R e)

end
end StatMech.FrontierD
