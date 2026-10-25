/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenRootOffsetBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootGapFirstOrder
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFinite.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeDensityInvWidthConstant
    (c : Real) (r : Nat) : Real :=
  sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r
      (sixVertexTailFiniteDensityFloor c) /
    (1 - sixVertexRootDensityContractionRate c)

end
end StatMech.FrontierD
