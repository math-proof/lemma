/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalSeamCutCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalSeamCutCode.Part3


namespace StatMech.FrontierD

noncomputable section

structure SixVertexCanonicalSameStrandCutCode (T : EvenTorus) where
  arcs : SixVertexDirectedComplementaryArcPair T
  firstSeamEdge : SixVertexTorusEdge T
  secondSeamEdge : SixVertexTorusEdge T
  first_shape : firstSeamEdge.1 = 1 ∧
    firstSeamEdge.2.2 = svFinLast T.height_pos
  second_shape : secondSeamEdge.1 = 1 ∧
    secondSeamEdge.2.2 = svFinLast T.height_pos
  seam_ne : firstSeamEdge ≠ secondSeamEdge
  first_marked : (arcs.first.edge arcs.first.firstIndex).physical =
    sixVertexTorusEdgePhysical firstSeamEdge
  second_marked : (arcs.second.edge arcs.second.firstIndex).physical =
    sixVertexTorusEdgePhysical secondSeamEdge


end
end StatMech.FrontierD
