/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hseparate : ¬ (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree first)))
    (j : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree second))) :
    (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree first i).1.1.1 ≠
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree second j).1.1.1 := by
  intro hvertex
  have hdart :
      sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree first i =
        sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree second j :=
    sixVertexOrientedDisagreementDart_vertex_injective
      homega heta hdegree hvertex
  have hfirst := sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    homega heta hdegree first i
  have hsecond := sixVertexDegreeTwoStrandCycleEnumeration_sameCycle
    homega heta hdegree second j
  rw [hdart] at hfirst
  exact hseparate (hfirst.trans hsecond.symm)


end
end StatMech.FrontierD
