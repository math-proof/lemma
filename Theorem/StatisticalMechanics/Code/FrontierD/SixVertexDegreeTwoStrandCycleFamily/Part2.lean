/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.separateCycles_or_sameCycle
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    (¬ (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed.first seed.second) ∨
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle seed.first seed.second := by
  by_cases hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed.first seed.second
  · exact Or.inr hsame
  · exact Or.inl hsame

end
end StatMech.FrontierD
