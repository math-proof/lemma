/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part2


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoStrandPositiveNonzeroIndices
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Finset (Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) := by
  classical
  exact Finset.univ.filter fun i =>
    i ≠ sixVertexDegreeTwoStrandCycleZeroIndex
      homega heta hdegree seed ∧
      sixVertexDegreeTwoStrandStepSeamSign hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) = 1

end
end StatMech.FrontierD
