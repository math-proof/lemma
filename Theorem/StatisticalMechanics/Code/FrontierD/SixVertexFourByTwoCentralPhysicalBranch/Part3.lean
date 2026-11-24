module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 5000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoCentralRawMatching_certificate :
    Function.Injective sixVertexFourByTwoCentralRawMatching ∧
      ∀ source,
        (sixVertexFourByTwoCentralRawMatching source).1 ≠
            (sixVertexFourByTwoCentralRawMatching source).2 ∧
          sixVertexFourByTwoCentralSourceGrade source =
            sixVertexFourByTwoCentralRawTargetGrade
              (sixVertexFourByTwoCentralRawMatching source) := by
  decide +revert

end
end StatMech.FrontierD
