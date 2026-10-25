/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part6
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSeparateStrandCycleFamily
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (first second : SixVertexOrientedDisagreementDart omega eta)
    (hseparate : ¬ (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle first second) :
    SixVertexAtMostTwoCycleFamily T where
  count := 2
  count_le_two := by omega
  cycle i := ![
    sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree first,
    sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree second] i
  tail_disjoint := by
    intro i j hij a b
    fin_cases i <;> fin_cases j
    · simp at hij
    · rw [bne_iff_ne]
      intro htail
      apply sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
        homega heta hdegree first second hseparate a b
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree] using
        htail
    · rw [bne_iff_ne]
      intro htail
      apply sixVertexDegreeTwoStrandCycleEnumeration_vertex_ne
        homega heta hdegree first second hseparate b a
      symm
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree] using
        htail
    · simp at hij


end
end StatMech.FrontierD
