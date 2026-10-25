/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part6


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexFixedChargeDensityInvWidthConstantOfLower
    (c : Real) (r : Nat) (lower : Real) : Real :=
  sixVertexFixedChargeDensityStabilityErrorOfLower c 1 r lower /
    (1 - sixVertexRootDensityContractionRate c)

end
end StatMech.FrontierD
