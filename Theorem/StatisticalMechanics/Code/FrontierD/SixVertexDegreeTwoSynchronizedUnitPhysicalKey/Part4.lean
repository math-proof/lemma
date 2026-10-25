/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree
        component layer (doubledAlignedVertex x) =
      (sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
          component x !=
        (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta
            hdegree component x &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask,
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch,
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active]

@[simp] theorem sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree
      component layer v = false := by
  have hnot : ¬ (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 := by omega
  simp [sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask,
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex,
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex, hnot]


end
end StatMech.FrontierD
