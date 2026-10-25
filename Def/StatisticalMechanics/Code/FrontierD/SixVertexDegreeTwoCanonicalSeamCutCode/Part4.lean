/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode


namespace StatMech.FrontierD

noncomputable section

def sixVertexDecodeVerticalPhysicalEdge {T : EvenTorus}
    (physical : Bool × T.Vertex) : SixVertexTorusEdge T :=
  (1, physical.2)

end
end StatMech.FrontierD
