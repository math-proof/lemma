module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalConvergence
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenOffsetNodalNonperiodic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexEvenOffsetNodalErrorOfTest
    (c : Real) (s N : Nat) (testError : Real) : Real :=
  sixVertexEvenOffsetResidualError c s N +
    sixVertexEvenOffsetBoundaryError c s N +
    sixVertexEvenOffsetSourceMoveError c s N +
    (2 * s : Real) * testError

end
end StatMech.FrontierD
