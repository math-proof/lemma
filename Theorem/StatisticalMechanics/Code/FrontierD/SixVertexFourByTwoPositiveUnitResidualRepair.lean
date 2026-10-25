/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoPositiveUnitResidualRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoPositiveUnitResidualRepair


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoActiveObstructionResidualGeometricRepair_supported :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionToken
      sixVertexFourByTwoActiveObstructionResidualGeometricRepair.target :=
  sixVertexFourByTwoActiveObstructionResidualGeometricRepair.supported

end
end StatMech.FrontierD
