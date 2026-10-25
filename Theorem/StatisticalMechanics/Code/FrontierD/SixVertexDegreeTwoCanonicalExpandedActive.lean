/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalSelected_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle (cut.cutRight.head hright) = false ∧
      sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle
        ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have h := cut.rightHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright
  simpa [sixVertexDegreeTwoCanonicalSelected, h.1, h.2]

theorem sixVertexDegreeTwoCanonicalSelected_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle (cut.cutLeft.head hleft) = true ∧
      sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle
        ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutLeft.head hleft)) = false := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have h := cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright
  simpa [sixVertexDegreeTwoCanonicalSelected, h.1, h.2]

@[simp] theorem sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

@[simp] theorem sixVertexDegreeTwoCanonicalTransitionMask_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

theorem sixVertexDegreeTwoCanonicalTransitionMask_proper
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (v : T.Vertex) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v =
      (decide (v = doubledAlignedVertex (cut.cutRight.head hright)) ||
        decide (v = doubledAlignedVertex (cut.cutLeft.head hleft))) := by
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

theorem sixVertexDegreeTwoCanonicalSelectedVertex_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true := by
  rcases x with ⟨dx, branch⟩
  let v := doubledAlignedVertex (dx, branch)
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree dx.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = dx := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d dx rfl
  unfold sixVertexDegreeTwoCanonicalSelectedVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = dx
    at hd
  rw [hd]
  cases branch <;> simp_all

theorem sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) =
      (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle) ||
        decide (doubledAlignedBranchSwap x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle)) := by
  rcases x with ⟨dx, branch⟩
  let v := doubledAlignedVertex (dx, branch)
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree dx.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = dx := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d dx rfl
  unfold sixVertexDegreeTwoCanonicalSelectedVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = dx at hd
  rw [hd]
  cases branch <;> simp [doubledAlignedBranchSwap, Bool.or_comm]

theorem sixVertexDegreeTwoCanonicalSelectedVertex_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true ↔
      x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle ∨
        doubledAlignedBranchSwap x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle := by
  rw [sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership]
  simp

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) =
      let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
        hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x)
      let selected :=
        (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
            hdegree middle homegaSector hetaSector hmiddle) ||
          decide (doubledAlignedBranchSwap x ∈
            SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
              homegaSector hetaSector hmiddle))
      transition != ((transition && !selected) ||
        (selected &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold sixVertexDegreeTwoCanonicalExpandedRetieMask
  rw [sixVertexDegreeTwoCanonicalCorrectionMask_active homega heta hdegree
      middle homegaSector hetaSector hmiddle layer v hactive,
    sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]

@[simp] theorem sixVertexDegreeTwoCanonicalSelectedVertex_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have hmem := (cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright).1
  exact sixVertexDegreeTwoCanonicalSelectedVertex_of_mem homega heta hdegree
    middle homegaSector hetaSector hmiddle (cut.cutLeft.head hleft) hmem

@[simp] theorem sixVertexDegreeTwoCanonicalSelectedVertex_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  change sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle
      (doubledAlignedVertex (cut.cutRight.head hright)) = true
  change doubledAlignedVertex (cut.cutRight.head hright) =
      doubledAlignedVertex (cut.cutLeft.head hleft) at hvertex
  rw [hvertex]
  exact sixVertexDegreeTwoCanonicalSelectedVertex_leftHead homega heta hdegree
    middle homegaSector hetaSector hmiddle hleft hright

theorem sixVertexDegreeTwoCanonicalCorrectionMask_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) =
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  have hcorrection := sixVertexDegreeTwoCanonicalCorrectionMask_active homega
    heta hdegree middle homegaSector hetaSector hmiddle layer v hactive
  have hselected := sixVertexDegreeTwoCanonicalSelectedVertex_of_mem homega
    heta hdegree middle homegaSector hetaSector hmiddle x hx
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v =
    ((sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
      !sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v) ||
      (sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
        ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) at hcorrection
  rw [hselected, hd] at hcorrection
  simpa using hcorrection

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let left := cut.cutLeft.head hleft
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex left) =
      !((orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let left := cut.cutLeft.head hleft
  have hmem := (cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright).1
  change (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle (doubledAlignedVertex left) !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer (doubledAlignedVertex left)) = _
  rw [sixVertexDegreeTwoCanonicalTransitionMask_leftHead homega heta hdegree
      middle homegaSector hetaSector hmiddle hleft hright,
    sixVertexDegreeTwoCanonicalCorrectionMask_of_mem homega heta hdegree
      middle homegaSector hetaSector hmiddle layer left hmem]
  cases (orientedDartAlignedRetie homega heta hdegree left.1).pairingP <;>
    cases (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ <;>
    decide

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle
        (doubledAlignedVertex right)
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) =
      (selected && !mismatch) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let v := doubledAlignedVertex right
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree right.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = right.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d right.1 rfl
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hcorrection := sixVertexDegreeTwoCanonicalCorrectionMask_active homega
    heta hdegree middle homegaSector hetaSector hmiddle layer v hactive
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v =
    ((sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
      !sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v) ||
      (sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
        ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) at hcorrection
  change (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v) = _
  rw [htransition] at hcorrection
  rw [htransition, hcorrection, hd]
  cases sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle v <;>
    cases (orientedDartAlignedRetie homega heta hdegree right.1).pairingP <;>
    cases (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ <;>
    decide

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) =
      !((orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  have hbranch :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  have hleftMask := sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer
  change sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) = _
  change (cut.cutLeft.head hleft) = doubledAlignedBranchSwap right at hbranch
  have hfirst : (cut.cutLeft.head hleft).1 = right.1 := by
    simpa [doubledAlignedBranchSwap] using congrArg
      (fun z : DoubledAlignedState omega eta => z.1) hbranch
  dsimp only at hleftMask
  rw [hfirst] at hleftMask
  rw [hvertex]
  exact hleftMask


theorem sixVertexDegreeTwoCanonicalTransportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
            homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
          homegaSector hetaSector hmiddle x then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [sixVertexDegreeTwoAlignedTransportedColor_active]
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
      hdegree middle homegaSector hetaSector hmiddle
  · simp [sixVertexDegreeTwoCanonicalSelected, hx]
  · simp [sixVertexDegreeTwoCanonicalSelected, hx]

end
end StatMech.FrontierD
