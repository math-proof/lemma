/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusLocalSwitchMask_agreement
    {T : EvenTorus} (omega eta : SixVertexArrows T) (v : T.Vertex) :
    sixVertexTorusLocalSwitchMask (sixVertexTorusAgreementMask omega eta) v =
      sixVertexLocalAgreementMask
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) := by
  funext side
  fin_cases side <;>
    simp [sixVertexTorusLocalSwitchMask, sixVertexTorusAgreementMask,
      sixVertexLocalAgreementMask, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming]


theorem sixVertexLocalAgreementMask_balanced
    (first second : SixVertexLocalIncomingPattern)
    (hfirst : first.Ice) (hsecond : second.Ice)
    (hdegree : (sixVertexLocalDisagreementSides first second).card = 0 \/
      (sixVertexLocalDisagreementSides first second).card = 2) :
    SixVertexLocalBalancedFlipMask first
      (sixVertexLocalAgreementMask first second) := by
  simp only [SixVertexLocalBalancedFlipMask,
    SixVertexLocalIncomingPattern.Ice,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    sixVertexLocalIncomingCount,
    sixVertexLocalAgreementMask,
    sixVertexLocalDisagreementSides] at *
  decide +revert

theorem sixVertexLocalAgreementMask_comm
    (first second : SixVertexLocalIncomingPattern) :
    sixVertexLocalAgreementMask first second =
      sixVertexLocalAgreementMask second first := by
  funext side
  simp [sixVertexLocalAgreementMask, eq_comm]


theorem sixVertexTorusAgreementMask_balanced_first
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexBalancedFlipMask omega
      (sixVertexTorusAgreementMask omega eta) := by
  intro v
  rw [sixVertexTorusLocalSwitchMask_agreement]
  exact sixVertexLocalAgreementMask_balanced _ _
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (sixVertexLocalIncomingPattern_ice eta heta v)
    (hdegree v)


theorem sixVertexTorusAgreementMask_balanced_second
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexBalancedFlipMask eta
      (sixVertexTorusAgreementMask omega eta) := by
  intro v
  rw [sixVertexTorusLocalSwitchMask_agreement]
  have h := sixVertexLocalAgreementMask_balanced
    (sixVertexLocalIncomingPattern eta v)
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern_ice eta heta v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (by
      simpa [sixVertexLocalDisagreementSides, ne_comm] using hdegree v)
  rw [sixVertexLocalAgreementMask_comm]
  exact h


theorem sixVertexTorusFlip_agreement_ice_first
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) omega).IceRule :=
  sixVertexTorusFlip_ice_of_balanced homega
    (sixVertexTorusAgreementMask_balanced_first homega heta hdegree)

theorem sixVertexTorusFlip_agreement_ice_second
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexTorusFlip (sixVertexTorusAgreementMask omega eta) eta).IceRule :=
  sixVertexTorusFlip_ice_of_balanced heta
    (sixVertexTorusAgreementMask_balanced_second homega heta hdegree)


end
end StatMech.FrontierD
