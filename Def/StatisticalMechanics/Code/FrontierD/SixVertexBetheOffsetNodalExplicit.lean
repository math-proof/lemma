module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalConvergence
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenOffsetNodalNonperiodic


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalExplicit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexContinuousOffsetFourierBound (c : Real) : Real :=
  (sixVertexOffsetRapidityLipschitzNNReal
    (sixVertexAntiferroelectricLambda c) : Real) * Real.pi

end
end StatMech.FrontierD
