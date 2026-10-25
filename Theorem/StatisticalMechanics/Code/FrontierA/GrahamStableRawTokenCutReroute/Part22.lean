/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part21
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawDirectAlternateLeftToken_source_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source ∧
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = owner) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source ∧
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = s.source) := by
  classical
  dsimp only
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  split
  next hsourceSelf =>
    left
    refine ⟨hsourceSelf, ?_⟩
    split <;> rfl
  next hsourceSelf =>
    exact Or.inr ⟨hsourceSelf, rfl⟩

theorem canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) s := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsourceNew : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).1
  have hownerNew : CanonicalRawGateRelated ends m j k l zero p
      owner.1 (next s).target.1 :=
    (canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s).2.1
  have hownerOld : CanonicalRawGateRelated ends m j k l zero p
      owner.1 s.target.1 :=
    canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  rw [canonicalStableRawDirectAlternateLeftToken]
  dsimp only
  split
  next hsourceSelf =>
    split
    next hownerSelf => exact ⟨Or.inr rfl, hsourceNew, hownerNew⟩
    next hownerSelf => exact ⟨Or.inr rfl, s.related, hownerOld⟩
  next hsourceSelf => exact ⟨Or.inl rfl, hsourceNew, hownerNew⟩

theorem canonicalStableRawDirectAlternateLeftToken_ne_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hdirect ≠
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  intro htoken
  unfold canonicalStableRawStateLeftToken at htoken
  rw [dif_neg hdirect] at htoken
  rw [canonicalStableRawDirectAlternateLeftToken] at htoken
  dsimp only at htoken
  split at htoken
  next hsourceSelf =>
    split at htoken
    next hownerSelf =>
      exact s.exceptional (congrArg (fun token => token.1.1) htoken).symm
    next hownerSelf =>
      exact s.exceptional (congrArg (fun token => token.1.1) htoken).symm
  next hsourceSelf =>
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact congrArg (fun token => token.2.1) htoken

theorem canonicalStableRawDirectAlternateLeftToken_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawDirectAlternateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  exact canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno _ s
      (canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)


theorem card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset ↑(canonicalRawCommonClosure ends m j k l zero p))
    (r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hfiber : ∀ c ∈ S,
      canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r) :
    S.card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (S.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let toLeft : ↑(canonicalRawCommonClosure ends m j k l zero p) ->
      leftMaskFiber ends m j k l zero p := fun c =>
    sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1
      (canonicalRawCommonClosure_leftGate
        ends m j k l zero p c.1 c.2)
  let leftS : Finset (leftMaskFiber ends m j k l zero p) := S.image toLeft
  have htoLeft : Function.Injective toLeft := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : leftMaskFiber ends m j k l zero p => x.1.1) hcd
  have hleftCard : leftS.card = S.card := by
    exact Finset.card_image_of_injective S htoLeft
  have himage : ∀ c ∈ leftS,
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p (toLeft r) (toLeft r)
          (canonicalTransferWorks_self hloop hjk hkl hk0 (toLeft r))).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p c c
            (canonicalTransferWorks_self hloop hjk hkl hk0 c)).1.1 := by
    intro c hc
    obtain ⟨cRaw, hcRaw, rfl⟩ := Finset.mem_image.mp hc
    let e := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p
    let qr := canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)
    let qc := canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p cRaw.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p cRaw.1 cRaw.2)
    have heqRaw := hfiber cRaw hcRaw
    have heq : e qr = e qc := by
      apply Subtype.ext
      change canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p r =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p cRaw
      exact heqRaw.symm
    exact congrArg (fun q : rightMaskFiber ends m j k l zero p => q.1.1)
      (e.injective heq)
  have hcanonical :=
    card_le_canonicalMaskRightNeighborhood_of_selfImageFiber
      ends m j k l zero hloop hjk hkl hk0 p leftS (toLeft r) himage
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let rawS : Finset (leftSourceMaskFiber ends m j k l zero p) :=
    S.map ⟨Subtype.val, Subtype.val_injective⟩
  let rawNeighborhood := StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p) rawS
  let rawTargetValue :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS) ->
        leftSourceMaskFiber ends m j k l zero p := fun q => (e q.1).1
  have rawTargetValue_mem (q :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS)) :
      rawTargetValue q ∈ rawNeighborhood := by
    let d := rawTargetValue q
    have hq := (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p leftS q.1).1 q.2
    obtain ⟨c, hcLeft, hqc⟩ := hq
    obtain ⟨cRaw, hcRaw, hc⟩ := Finset.mem_image.mp hcLeft
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ d, cRaw.1, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨cRaw, hcRaw, rfl⟩
    refine ⟨canonicalRawCommonClosure_leftGate
        ends m j k l zero p cRaw.1 cRaw.2, (e q.1).2, ?_⟩
    have hcEq : c = toLeft cRaw := hc.symm
    have heqGate :
        (⟨d, (e q.1).2⟩ : reversedRightSourceMaskGateFiber
          ends m j k l zero p) = e q.1 := by
      apply Subtype.ext
      rfl
    rw [heqGate, e.symm_apply_apply]
    simpa only [hcEq] using hqc
  let rawTarget :
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p leftS) ->
        ↑rawNeighborhood := fun q => ⟨rawTargetValue q, rawTargetValue_mem q⟩
  have hrawTarget : Function.Injective rawTarget := by
    intro q₁ q₂ hq
    have hval := congrArg Subtype.val hq
    change (e q₁.1).1 = (e q₂.1).1 at hval
    have he : e q₁.1 = e q₂.1 := Subtype.ext hval
    exact Subtype.ext (e.injective he)
  have hrightCard :
      (canonicalMaskRightNeighborhood ends m j k l zero p leftS).card ≤
        rawNeighborhood.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective rawTarget hrawTarget
  rw [← hleftCard]
  exact hcanonical.trans hrightCard


end StatMech.GrahamGHS.FourColor
