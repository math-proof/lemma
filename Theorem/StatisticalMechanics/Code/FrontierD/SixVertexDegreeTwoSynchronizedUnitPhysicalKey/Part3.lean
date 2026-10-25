/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex homega heta
        hdegree component (doubledAlignedVertex x) =
      (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
          component x &&
        ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  unfold sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta
      (doubledAlignedVertex x) hactive = x.1 at hdart
  rw [hdart]


end
end StatMech.FrontierD
