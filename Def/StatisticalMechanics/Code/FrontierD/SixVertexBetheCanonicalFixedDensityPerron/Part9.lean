module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexHalfDensityInvWidthConstantOfLower
    (c lower : Real) : Real :=
  sixVertexFiniteDensityContinuumErrorOfLower c 1 lower /
    (1 - sixVertexRootDensityContractionRate c)

end
end StatMech.FrontierD
