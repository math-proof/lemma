/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalWindingCirculation_isCirculation
    {T : EvenTorus} (row : Fin T.height) (coefficient : Int) :
    SixVertexTorusCirculation T
      (sixVertexHorizontalWindingCirculation row coefficient).1
      (sixVertexHorizontalWindingCirculation row coefficient).2 := by
  intro v
  simp [sixVertexHorizontalWindingCirculation]


end
end StatMech.FrontierD
