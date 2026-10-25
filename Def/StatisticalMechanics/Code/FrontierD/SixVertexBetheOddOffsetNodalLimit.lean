/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetNodalLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetBoundaryEstimate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddRootOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetSymmetry
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetWeightedResidual


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexOddOffsetUniformBound (c : Real) (s : Nat) : Real :=
  ((1 / 2 : Real) + Real.pi *
      (sixVertexFixedChargeDensityInvWidthConstant c 0 +
        sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) /
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c)) /
    sixVertexTailFiniteDensityFloor c

def sixVertexOddOffsetResidualError (c : Real) (s N : Nat) : Real :=
  4 * sixVertexThetaTaylorBound c *
    sixVertexOddOffsetUniformBound c s ^ 2 / N

def sixVertexOddOffsetBoundaryError (c : Real) (s N n : Nat) : Real :=
  (2 * s + 1 : Real) *
      (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((N : Real) * sixVertexTailFiniteDensityFloor c) +
    (n : Real) * sixVertexThetaTaylorBound c /
      (((N : Real) * sixVertexTailFiniteDensityFloor c) ^ 2)

def sixVertexOddOffsetSourceMoveError (c : Real) (s N : Nat) : Real :=
  (2 * s + 1 : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexOddOffsetUniformBound c s / N)

def sixVertexOddOffsetNodalError
    (c : Real) (s N n : Nat) (testError : Real) : Real :=
  sixVertexOddOffsetResidualError c s N +
    sixVertexOddOffsetBoundaryError c s N n +
    sixVertexOddOffsetSourceMoveError c s N +
    (2 * s + 1 : Real) * testError

end
end StatMech.FrontierD
