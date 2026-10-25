/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem SixVertexCanonicalSameStrandCutCode.decodeSeamPair_eq
    {T : EvenTorus} (code : SixVertexCanonicalSameStrandCutCode T) :
    code.decodeSeamPair = (code.firstSeamEdge, code.secondSeamEdge) := by
  unfold SixVertexCanonicalSameStrandCutCode.decodeSeamPair
  rw [code.first_marked, code.second_marked,
    sixVertexDecodeVerticalPhysicalEdge_leftInverse _ code.first_shape.1,
    sixVertexDecodeVerticalPhysicalEdge_leftInverse _ code.second_shape.1]


theorem SixVertexCanonicalSameStrandCutCode.seamPair_eq_of_arcs_eq
    {T : EvenTorus} (first second : SixVertexCanonicalSameStrandCutCode T)
    (harcs : first.arcs = second.arcs) :
    (first.firstSeamEdge, first.secondSeamEdge) =
      (second.firstSeamEdge, second.secondSeamEdge) := by
  rw [← first.decodeSeamPair_eq, ← second.decodeSeamPair_eq]
  unfold SixVertexCanonicalSameStrandCutCode.decodeSeamPair
  rw [harcs]


end
end StatMech.FrontierD
