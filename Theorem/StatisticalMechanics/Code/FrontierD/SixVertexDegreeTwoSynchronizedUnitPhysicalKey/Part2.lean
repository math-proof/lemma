/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree
        component (doubledAlignedVertex x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (x.1, false) := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta
      (doubledAlignedVertex x) hactive = x.1 at hdart
  rw [hdart]


theorem sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree
        component (doubledAlignedVertex x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component x := by
  rw [sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active]
  rcases x with ⟨dart, branch⟩
  cases branch
  · rfl
  · exact sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches
      homega heta hdegree component dart


end
end StatMech.FrontierD
