/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOffsetBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetSymmetry
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalEvenOffsetUniformBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  Real.pi *
      (sixVertexHalfDensityInvWidthConstantOfLower c
          (sixVertexCanonicalHalfDensityFloor hc) +
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s)
          (sixVertexCanonicalFixedEvenDensityFloor hc s)) /
    (((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) *
      sixVertexCanonicalFixedEvenDensityFloor hc s)

def sixVertexCanonicalOddOffsetUniformBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  ((1 / 2 : Real) + Real.pi *
      (sixVertexHalfDensityInvWidthConstantOfLower c
          (sixVertexCanonicalHalfDensityFloor hc) +
        sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1)
          (sixVertexCanonicalFixedOddDensityFloor hc s)) /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) /
    sixVertexCanonicalFixedOddDensityFloor hc s

end
end StatMech.FrontierD
