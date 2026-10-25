/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalPositiveSeamPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFamily.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoStrandCycleZeroIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed)) :=
  ⟨0, orderOf_pos (sixVertexDegreeTwoStrandCyclePerm
    homega heta hdegree seed)⟩


end
end StatMech.FrontierD
