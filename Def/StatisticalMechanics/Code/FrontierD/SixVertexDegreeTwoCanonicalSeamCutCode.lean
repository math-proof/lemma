/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusEdgePhysical {T : EvenTorus}
    (edge : SixVertexTorusEdge T) : Bool × T.Vertex :=
  if edge.1 = 0 then (false, edge.2) else (true, edge.2)

end
end StatMech.FrontierD
