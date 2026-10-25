/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_physical
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).physical =
      sixVertexTorusEdgePhysical edge := by
  rcases edge with ⟨direction, vertex⟩
  fin_cases direction <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical, sixVertexTorusEdgePhysical]


end
end StatMech.FrontierD
