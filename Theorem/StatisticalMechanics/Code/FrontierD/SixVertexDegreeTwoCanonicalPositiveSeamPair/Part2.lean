/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoStrandCycleEnumeration_position
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart) :
    sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed
        (sixVertexDegreeTwoStrandCyclePosition
          homega heta hdegree seed dart hsame) = dart := by
  exact congrArg Subtype.val
    ((sixVertexDegreeTwoStrandCycleEnumerationEquiv
      homega heta hdegree seed).apply_symm_apply _)

theorem sixVertexDegreeTwoStrandCyclePosition_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart)
    (hne : seed ≠ dart) :
    sixVertexDegreeTwoStrandCyclePosition
      homega heta hdegree seed dart hsame ≠
        sixVertexDegreeTwoStrandCycleZeroIndex homega heta hdegree seed := by
  intro hzero
  apply hne
  rw [← sixVertexDegreeTwoStrandCycleEnumeration_position
    homega heta hdegree seed dart hsame, hzero,
    sixVertexDegreeTwoStrandCycleEnumeration_zero]


end
end StatMech.FrontierD
