/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 1000000 in


noncomputable def sixVertexDegreeTwoStrandCyclePosition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
  (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed).symm
      ⟨dart, by
        rw [Equiv.Perm.mem_support]
        unfold sixVertexDegreeTwoStrandCyclePerm
        rw [Equiv.Perm.cycleOf_apply, if_pos hsame]
        exact sixVertexOrientedDegreeTwoStrandSuccessor_ne
          homega heta hdegree dart⟩

end
end StatMech.FrontierD
