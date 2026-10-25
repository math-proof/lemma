/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddOffsetLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLinearBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddOffsetLinear


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalOddOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  let E0 := sixVertexHalfDensityInvWidthConstantOfLower c
    (sixVertexCanonicalHalfDensityFloor hc)
  let Er := sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
    (sixVertexCanonicalFixedOddDensityFloor hc s)
  ((E0 + Er) /
    ((sixVertexAnisotropyMagnitude c - 1) /
      sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedOddDensityFloor hc s

def sixVertexCanonicalOddOffsetRemainderBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
    (4 * sixVertexCanonicalHalfDensityFloor hc ^ 2 *
      sixVertexCanonicalFixedOddDensityFloor hc s)

end
end StatMech.FrontierD
