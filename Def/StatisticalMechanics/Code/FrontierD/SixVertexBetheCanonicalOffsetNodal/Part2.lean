/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetNodal.Part2


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalEvenOffsetNodalError
    (c : Real) (hc : 2 < c) (s N : Nat) (testError : Real) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexCanonicalEvenOffsetUniformBound c hc s ^ 2 / N +
    2 * (s : Real) ^ 2 *
        (sixVertexThetaRightLipschitzNNReal c : Real) /
      ((N : Real) * sixVertexCanonicalHalfDensityFloor hc) +
    (2 * s : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexCanonicalEvenOffsetUniformBound c hc s / N) +
    (2 * s : Real) * testError

def sixVertexCanonicalOddOffsetNodalError
    (c : Real) (hc : 2 < c) (s N n : Nat) (testError : Real) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexCanonicalOddOffsetUniformBound c hc s ^ 2 / N +
    ((2 * s + 1 : Real) *
          (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((N : Real) * sixVertexCanonicalHalfDensityFloor hc) +
      (n : Real) * sixVertexThetaTaylorBound c /
        (((N : Real) * sixVertexCanonicalHalfDensityFloor hc) ^ 2)) +
    (2 * s + 1 : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexCanonicalOddOffsetUniformBound c hc s / N) +
    (2 * s + 1 : Real) * testError

end
end StatMech.FrontierD
