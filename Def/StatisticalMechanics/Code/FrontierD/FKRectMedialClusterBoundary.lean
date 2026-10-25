/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectMedialDartAtPrimalVertex (R : FKRectTorus) (x : R.Vertex) :
    FKMedialDart R.medialTorus :=
  let e : R.EdgeIndex := (true, x)
  if Even x.2.val then
    fkMedialWestDart (fkRectMedialVertexOfEdge R e)
  else
    fkMedialEastDart (fkRectMedialVertexOfEdge R e)

end
end StatMech.FrontierD
