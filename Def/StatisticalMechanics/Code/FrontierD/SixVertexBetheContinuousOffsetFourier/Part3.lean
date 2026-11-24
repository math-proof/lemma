module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexContinuousOffsetFourier
    (c : Real) (hc : 2 < c) (x : Real) : Real :=
  sixVertexOffsetRapidityProfile (sixVertexAntiferroelectricLambda c)
    (sixVertexMomentumRapidity (sixVertexAntiferroelectricLambda c)
      (sixVertexAntiferroelectricLambda_pos hc) x)

end
end StatMech.FrontierD
