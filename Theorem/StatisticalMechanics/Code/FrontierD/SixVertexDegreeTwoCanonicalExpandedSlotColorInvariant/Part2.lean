/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      fkMedialTogglePairingMask
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (fun v => sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree
            middle homegaSector hetaSector hmiddle v !=
          sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
            homegaSector hetaSector hmiddle layer v) := by
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing,
    sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask,
    fkMedialTogglePairingMask_compose]

theorem sixVertexDegreeTwoCanonicalCorrectionMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer v =
      ((transition && !selected) ||
        (selected &&
          ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) := by
  simp [sixVertexDegreeTwoCanonicalCorrectionMask,
    sixVertexDegreeTwoCanonicalInternalMismatchVertex, hactive]


@[simp] theorem sixVertexDegreeTwoCanonicalCorrectionMask_layer_independent
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (first second : Bool) (v : T.Vertex) :
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle first v =
      sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle second v := by
  rfl


theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
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
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then
          if transition then !retie.pairingQ else retie.pairingQ
        else retie.pairingP,
        if selected then
          if transition then !retie.pairingP else retie.pairingP
        else retie.pairingQ) := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have hfalse := congrFun
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask homega heta
      hdegree middle homegaSector hetaSector hmiddle false) v
  have htrue := congrFun
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask homega heta
      hdegree middle homegaSector hetaSector hmiddle true) v
  have hP := alignedRoutingPairing_eq_at_active homega heta hdegree false v
    hactive
  have hQ := alignedRoutingPairing_eq_at_active homega heta hdegree true v
    hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
    retie.pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
    retie.pairingQ at hQ
  have hcorrectionFalse := sixVertexDegreeTwoCanonicalCorrectionMask_active
    homega heta hdegree middle homegaSector hetaSector hmiddle false v hactive
  have hcorrectionTrue := sixVertexDegreeTwoCanonicalCorrectionMask_active
    homega heta hdegree middle homegaSector hetaSector hmiddle true v hactive
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle false v =
    ((transition && !selected) ||
      (selected && (retie.pairingP != retie.pairingQ))) at hcorrectionFalse
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle true v =
    ((transition && !selected) ||
      (selected && (retie.pairingP != retie.pairingQ))) at hcorrectionTrue
  change sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle false v =
    (if transition !=
        sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle false v then
      !alignedRoutingLoopPairing homega heta hdegree false v
    else alignedRoutingLoopPairing homega heta hdegree false v) at hfalse
  change sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle true v =
    (if transition !=
        sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle true v then
      !alignedRoutingLoopPairing homega heta hdegree true v
    else alignedRoutingLoopPairing homega heta hdegree true v) at htrue
  rw [hP, hcorrectionFalse] at hfalse
  rw [hQ, hcorrectionTrue] at htrue
  change (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle false v,
    sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle true v) =
    (if selected then
        if transition then !retie.pairingQ else retie.pairingQ
      else retie.pairingP,
      if selected then
        if transition then !retie.pairingP else retie.pairingP
      else retie.pairingQ)
  rw [hfalse, htrue]
  cases transition <;> cases selected <;> cases retie.pairingP <;>
    cases retie.pairingQ <;> decide


theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_emptyCut_regression
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
    (hempty :
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutLeft = [] \/
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutRight = [])
    (hselected : sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree
      middle homegaSector hetaSector hmiddle v = true)
    (hmismatch :
      let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
      (orientedDartAlignedRetie homega heta hdegree d).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ = true) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (retie.pairingQ, retie.pairingP) /\
    (retie.pairingP != retie.pairingQ) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  have htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v = false := by
    rcases hempty with hleft | hright
    · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft]
    · by_cases hleft : cut.cutLeft = []
      · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft]
      · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft,
          hright]
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  change (_, _) =
    (if sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v then
      if sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle v then !retie.pairingQ
      else retie.pairingQ
    else retie.pairingP,
    if sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v then
      if sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle v then !retie.pairingP
      else retie.pairingP
    else retie.pairingQ) at htable
  constructor
  · simpa [htransition, hselected] using htable
  · exact hmismatch

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle layer) =
      sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer := by
  exact fkMedialTogglePairingMask_self _ _


end
end StatMech.FrontierD
