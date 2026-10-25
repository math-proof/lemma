/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (dart, false) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (dart, true) := by
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
  change
    (sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart !=
        sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component
            (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false dart)) =
      (sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart !=
        sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component
            (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true dart))
  rw [sixVertexDegreeTwoSynchronizedComponentSelector_predecessors]


theorem sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component =
      ∑ dart : SixVertexOrientedDisagreementDart omega eta,
        if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
            component dart then
          sixVertexDegreeTwoStrandStepSeamSign hdegree dart
        else 0 := by
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
    sixVertexDegreeTwoSynchronizedComponentSelector
  simp only [decide_eq_true_eq]


theorem sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
      component = 1) :
    (∑ dart : SixVertexOrientedDisagreementDart omega eta,
      if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
          component dart then
        sixVertexDegreeTwoStrandStepSeamSign hdegree dart
      else 0) = 1 := by
  rw [← sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum]
  exact hcharge

end
end StatMech.FrontierD
