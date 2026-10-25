/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoStrandCycleEnumerationEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed)) ≃
      (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed).support :=
  permCycleFinEquivSupport
    (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed)
    (sixVertexDegreeTwoStrandCyclePerm_isCycle
      homega heta hdegree seed)
    ⟨seed, sixVertexDegreeTwoStrandCyclePerm_seed_mem
      homega heta hdegree seed⟩

noncomputable def sixVertexDegreeTwoStrandCycleEnumeration
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
        homega heta hdegree seed)) →
      SixVertexOrientedDisagreementDart omega eta :=
  fun i => (sixVertexDegreeTwoStrandCycleEnumerationEquiv
    homega heta hdegree seed i).1

end
end StatMech.FrontierD
