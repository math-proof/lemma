/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoStrandPositiveNonzeroIndices_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed dart : SixVertexOrientedDisagreementDart omega eta)
    (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).SameCycle seed dart)
    (hne : seed ≠ dart)
    (hpositive : sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1) :
    (sixVertexDegreeTwoStrandPositiveNonzeroIndices
      homega heta hdegree seed).Nonempty := by
  classical
  refine ⟨sixVertexDegreeTwoStrandCyclePosition
    homega heta hdegree seed dart hsame, ?_⟩
  simp only [sixVertexDegreeTwoStrandPositiveNonzeroIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨sixVertexDegreeTwoStrandCyclePosition_ne_zero
      homega heta hdegree seed dart hsame hne,
    by simpa using hpositive⟩


end
end StatMech.FrontierD
