/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosedPhysicalFinKey_selected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoBranchClosedSelectedStateFinIndex homega heta
          hdegree middle homegaSector hetaSector hmiddle x hx) =
      if layer then
        (doubledAlignedVertex
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x))
      else
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
  unfold sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey
    sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey
    sixVertexDegreeTwoBranchClosedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree layer)
      (doubledAlignedBlackDart homega heta hdegree false x) = _
  cases layer
  · exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  · rw [← sixVertexDegreeTwoTauAdjustedState_trueDart
      homega heta hdegree x]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _


theorem sixVertexDegreeTwoBranchClosedPhysicalTargetPairing_noTransition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2)
    (htransition : sixVertexDegreeTwoBranchClosedTransitionVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v = false)
    (hselected :
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (orientedDisagreementDartAtActiveVertex homega heta v hactive,
          false) = true) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    (sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (retie.pairingQ, retie.pairingP) := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  have hP := alignedRoutingPairing_eq_at_active homega heta hdegree false v
    hactive
  have hQ := alignedRoutingPairing_eq_at_active homega heta hdegree true v
    hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
    retie.pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
    retie.pairingQ at hQ
  change ((if _ != _ then !_ else _), (if _ != _ then !_ else _)) = _
  rw [hP, hQ]
  simp [sixVertexDegreeTwoBranchClosedPhysicalRetieMask, htransition,
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex, hactive, hselected]
  cases retie.pairingP <;> cases retie.pairingQ <;> decide

end
end StatMech.FrontierD
