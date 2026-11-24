module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetBoundaryEstimate
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetDiscreteStability
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTestQuadrature
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenRootOffsetBound


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexEvenOffsetUniformBound (c : Real) (s : Nat) : Real :=
  Real.pi *
      (sixVertexFixedChargeDensityInvWidthConstant c 0 +
        sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) /
    (((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) *
      sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetResidualError
    (c : Real) (s N : Nat) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexEvenOffsetUniformBound c s ^ 2 / N

def sixVertexEvenOffsetBoundaryError
    (c : Real) (s N : Nat) : Real :=
  2 * (s : Real) ^ 2 *
      (sixVertexThetaRightLipschitzNNReal c : Real) /
    ((N : Real) * sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetSourceMoveError
    (c : Real) (s N : Nat) : Real :=
  (2 * s : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
    (sixVertexEvenOffsetUniformBound c s / N)

def sixVertexFixedChargeOffsetNetMargin
    (c : Real) (N r : Nat) : Real :=
  sixVertexRootDensityKernelFloor c *
      (sixVertexRootDensityScale c /
        (4 * (sixVertexAnisotropyMagnitude c + 1) *
          sixVertexFiniteRootDensityUniformBound c)) -
    sixVertexFixedChargeOffsetRowError c N r
      (sixVertexTailFiniteDensityFloor c)

def sixVertexEvenOffsetNodalError
    (c : Real) (s N : Nat) (G : Real) (D : NNReal) : Real :=
  sixVertexEvenOffsetResidualError c s N +
    sixVertexEvenOffsetBoundaryError c s N +
    sixVertexEvenOffsetSourceMoveError c s N +
    (2 * s : Real) * sixVertexFixedChargeOffsetTestError c N (2 * s)
      (sixVertexTailFiniteDensityFloor c) G D


end
end StatMech.FrontierD
