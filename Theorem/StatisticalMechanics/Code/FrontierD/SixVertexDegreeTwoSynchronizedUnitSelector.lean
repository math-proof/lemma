/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree
        component dart = true ↔
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        dart = component := by
  simp [sixVertexDegreeTwoSynchronizedComponentSelector]


theorem sixVertexDegreeTwoSynchronizedComponentSelector_predecessors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false dart) =
      sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true dart) := by
  unfold sixVertexDegreeTwoSynchronizedComponentSelector
  rw [decide_eq_decide]
  exact sixVertexDegreeTwoSynchronizedComponent_predecessors_iff
    homega heta hdegree component dart


end
end StatMech.FrontierD
