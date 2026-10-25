/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenRootOffsetIncrement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenRootOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalDensityLipschitz


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootGapFirstOrderConstant (c E : Real) : Real :=
  ((sixVertexFiniteRootDensityLipschitzConstant c : Real) *
      (1 / sixVertexTailFiniteDensityFloor c) ^ 2 +
    (1 / sixVertexTailFiniteDensityFloor c) *
      (E / ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c))) /
    sixVertexTailFiniteDensityFloor c


end
end StatMech.FrontierD
