/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalEvenOffsetLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLinearBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalEvenOffsetLinear


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalEvenOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  ((sixVertexHalfDensityInvWidthConstantOfLower c
        (sixVertexCanonicalHalfDensityFloor hc) +
      sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
        (sixVertexCanonicalFixedEvenDensityFloor hc s)) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedEvenDensityFloor hc s

end
end StatMech.FrontierD
