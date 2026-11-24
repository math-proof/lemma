module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalCoordinate
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourierPhysicalDensity
    (c : Real) (hc : 2 < c) (x : Real) : Real :=
  let lam := sixVertexAntiferroelectricLambda c
  sixVertexFourierRootDensity lam
      (sixVertexMomentumRapidity lam
        (sixVertexAntiferroelectricLambda_pos hc) x) /
    (2 * Real.pi * sixVertexRootDensityWeight c x)

end
end StatMech.FrontierD
