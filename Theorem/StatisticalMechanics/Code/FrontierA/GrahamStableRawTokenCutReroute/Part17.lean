/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part16
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawStateLeftToken_eq_imp
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno t ->
      s = t ∨
        CanonicalStableRawSelfDirectTokenCollision
          ends m j k l zero hloop hjk hkl hk0 p hno s t ∨
        CanonicalStableRawSelfDirectTokenCollision
          ends m j k l zero hloop hjk hkl hk0 p hno t s := by
  classical
  intro htoken
  by_cases hs : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source
  · by_cases ht : t.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source
    · left
      apply canonicalStableRawSelfReroutePredecessor_unique
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s) s t
      · refine ⟨hs, ?_⟩
        simpa only [canonicalStableRawStateLeftToken, dif_pos hs]
      · refine ⟨ht, ?_⟩
        simpa only [canonicalStableRawStateLeftToken, dif_pos hs,
          dif_pos ht] using htoken.symm
    · right
      left
      refine ⟨hs, ht, ?_⟩
      apply canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno s t hs ht
      simpa only [canonicalStableRawStateLeftToken, dif_pos hs,
        dif_neg ht] using htoken
  · by_cases ht : t.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source
    · right
      right
      refine ⟨ht, hs, ?_⟩
      apply canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno t s ht hs
      simpa only [canonicalStableRawStateLeftToken, dif_neg hs,
        dif_pos ht] using htoken.symm
    · left
      have hsub : (⟨s, hs⟩ : {u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
            u.target.1 ≠ canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p u.source}) = ⟨t, ht⟩ :=
        canonicalStableRawDirectLeftToken_injective
          ends m j k l zero hloop hjk hkl hk0 p (by
            simpa only [canonicalStableRawStateLeftToken, dif_neg hs,
              dif_neg ht] using htoken)
      exact congrArg Subtype.val hsub


theorem canonicalStableRawSelfDirectTokenCollision_of_token_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (self direct : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : self.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p self.source)
    (hdirect : direct.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p direct.source)
    (htoken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct) :
    CanonicalStableRawSelfDirectTokenCollision
      ends m j k l zero hloop hjk hkl hk0 p hno self direct := by
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno self direct htoken with
    heq | hcollision | hreverse
  · exfalso
    apply hdirect
    simpa only [← heq] using hself
  · exact hcollision
  · exact False.elim (hdirect hreverse.1)


theorem canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
    Function.Injective fun x => canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have collisionFalse (x y : C)
      (hcollision : CanonicalStableRawSelfDirectTokenCollision
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state x) (state y)) : False := by
    rcases hcollision with ⟨hself, hdirect,
      ⟨hnext, hstable⟩ | ⟨hadvanceCollision, hsource, htargetEq, hne⟩⟩
    · have ha := hadvance x
      simp only [CanonicalStableRawOwnerAdvancingStep] at ha
      apply (state x).exceptional
      calc
        (state x).source.1 = (next (state x)).source.1 :=
          congrArg Subtype.val hstable.1.symm
        _ = canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p (state x).target := ha
    · have hy : y = σ x := by
        apply htarget
        calc
          (state y).target = (next (state x)).target := htargetEq
          _ = (state (σ x)).target :=
            congrArg (fun edge => edge.target) (hstep x).symm
      have ha := hadvance x
      simp only [CanonicalStableRawOwnerAdvancingStep] at ha
      apply (state x).exceptional
      calc
        (state x).source.1 = (state y).source.1 :=
          (congrArg Subtype.val hsource).symm
        _ = (state (σ x)).source.1 := by rw [hy]
        _ = (next (state x)).source.1 :=
          congrArg (fun edge => edge.source.1) (hstep x)
        _ = canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p (state x).target := ha
  intro x y hxy
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) (state y) hxy with
    hstate | hcollision | hcollision
  · apply htarget
    exact congrArg (fun edge => edge.target) hstate
  · exact False.elim (collisionFalse x y hcollision)
  · exact False.elim (collisionFalse y x hcollision)


theorem canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    {C : Type*} [Fintype C] (root : C)
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
    Nonempty (C ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
  let f : C -> {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)} :=
    fun x => ⟨canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno (state x),
      (canonicalStableRawStateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)).trans
          (hcomponent x)⟩
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep htarget
      hadvance
  exact congrArg Subtype.val hxy


theorem canonicalStableRawExceptionalEdgeNext_twoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let hc := canonicalRawCommonClosure_leftGate
      ends m j k l zero p s.source.1 s.source.2
    let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
    let hb := canonicalRawCommonClosure_leftGate
      ends m j k l zero p b.1 b.2
    CanonicalTightTwoRowCollision ends m j k l zero p
      (sourceMaskGatePointToLeftMaskFiber
        ends m j k l zero p s.source.1 hc)
      (sourceMaskGatePointToLeftMaskFiber
        ends m j k l zero p b.1 hb) := by
  classical
  dsimp only
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p s.target,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p s.target⟩
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p s.source.1 s.source.2
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p s.source.1 hc
  let owner := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  obtain ⟨hcOld, hdOld, hqA⟩ := s.related
  obtain ⟨hbOld, _, hqOwner⟩ :=
    canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  obtain ⟨hANew, hOwnerNew, _⟩ :=
    canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s
  obtain ⟨_, htNew, hrA⟩ := hANew
  obtain ⟨_, _, hrOwner⟩ := hOwnerNew
  let rawEquiv := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  let q := rawEquiv.symm ⟨s.target.1, hdOld⟩
  let r := rawEquiv.symm ⟨t.target.1, htNew⟩
  have hqr : q ≠ r := by
    intro h
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    have hraw := congrArg rawEquiv h
    simpa only [q, r, rawEquiv, Equiv.apply_symm_apply] using
      (congrArg (fun x => x.1) hraw).symm
  refine ⟨q, r, hqr, ?_, ?_, ?_, ?_⟩
  · simpa only [q, a, rawEquiv] using hqA
  · simpa only [q, owner, b, rawEquiv] using hqOwner
  · simpa only [r, a, t, rawEquiv] using hrA
  · simpa only [r, owner, b, t, rawEquiv] using hrOwner


theorem exists_ownerStableSquare_collisionTokens_and_surplusTokens
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase,
      r0 ≠ r1 ∧
        ∃ l0 l1 : StatMech.FrontierA.bipartiteLeftSurplusToken
            R T leftBase,
          l0 ≠ l1 := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  let t := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let b : ↑T := ⟨rightBase s.target,
    canonicalStableRawPreferredRightBase_mem
      ends m j k l zero hloop hjk hkl hk0 p s.target⟩
  have hstable' : t.source = s.source ∧ rightBase t.target = b.1 := by
    simpa only [CanonicalStableRawOwnerStableStep, t, b, rightBase] using hstable
  obtain ⟨hsourceNew, hownerNew, _⟩ :=
    canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno s
  have hcOldMem : s.source.1 ∈ T.filter fun c => R c s.target.1 :=
    Finset.mem_filter.mpr ⟨s.source.2, s.related⟩
  have hcNewRelated : R s.source.1 t.target.1 := hsourceNew
  have hcNewMem : s.source.1 ∈ T.filter fun c => R c t.target.1 :=
    Finset.mem_filter.mpr ⟨s.source.2, hcNewRelated⟩
  have hcNewExceptional : s.source.1 ≠ rightBase t.target := by
    intro h
    apply t.exceptional
    rw [hstable'.1]
    exact h
  let r0 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase :=
    ⟨s.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨s.exceptional, hcOldMem⟩⟩⟩
  let r1 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase :=
    ⟨t.target, ⟨s.source.1, Finset.mem_erase.mpr
      ⟨hcNewExceptional, hcNewMem⟩⟩⟩
  have hr01 : r0 ≠ r1 := by
    intro h
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno s
    exact (congrArg (fun x => x.1.1) h).symm
  have hbOldRelated : R b.1 s.target.1 := by
    exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p s.target
  have hbNewRelated : R b.1 t.target.1 := hownerNew
  let cAlt := if s.target.1 = leftBase s.source then
      t.target.1 else s.target.1
  have hcAltRelated : R s.source.1 cAlt := by
    dsimp only [cAlt]
    split
    · exact hcNewRelated
    · exact s.related
  have hcAltNe : cAlt ≠ leftBase s.source := by
    dsimp only [cAlt]
    split
    next heq =>
      intro h
      apply canonicalStableRawExceptionalEdgeNext_target_ne
        ends m j k l zero hloop hjk hkl hk0 p hno s
      exact h.trans heq.symm
    next hne => exact hne
  let bAlt := if s.target.1 = leftBase b then
      t.target.1 else s.target.1
  have hbAltRelated : R b.1 bAlt := by
    dsimp only [bAlt]
    split
    · exact hbNewRelated
    · exact hbOldRelated
  have hbAltNe : bAlt ≠ leftBase b := by
    dsimp only [bAlt]
    split
    next heq =>
      intro h
      apply canonicalStableRawExceptionalEdgeNext_target_ne
        ends m j k l zero hloop hjk hkl hk0 p hno s
      exact h.trans heq.symm
    next hne => exact hne
  let l0 : StatMech.FrontierA.bipartiteLeftSurplusToken
      R T leftBase :=
    ⟨s.source, ⟨cAlt, Finset.mem_erase.mpr ⟨hcAltNe,
      Finset.mem_filter.mpr ⟨Finset.mem_univ cAlt, hcAltRelated⟩⟩⟩⟩
  let l1 : StatMech.FrontierA.bipartiteLeftSurplusToken
      R T leftBase :=
    ⟨b, ⟨bAlt, Finset.mem_erase.mpr ⟨hbAltNe,
      Finset.mem_filter.mpr ⟨Finset.mem_univ bAlt, hbAltRelated⟩⟩⟩⟩
  have hcb : s.source ≠ b := by
    intro h
    apply s.exceptional
    exact congrArg Subtype.val h
  have hl01 : l0 ≠ l1 := by
    intro h
    exact hcb (congrArg Sigma.fst h)
  exact ⟨r0, r1, hr01, l0, l1, hl01⟩


theorem exists_two_collisionTokens_of_sameTarget_distinctSources
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) (hsource : s.source ≠ t.source) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase,
      r0 ≠ r1 := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  have htRelated : R t.source.1 s.target.1 := by
    simpa only [htarget] using t.related
  have htExceptional : t.source.1 ≠ rightBase s.target := by
    simpa only [htarget] using t.exceptional
  have hsMem : s.source.1 ∈
      (T.filter fun c => R c s.target.1).erase (rightBase s.target) :=
    Finset.mem_erase.mpr ⟨s.exceptional,
      Finset.mem_filter.mpr ⟨s.source.2, s.related⟩⟩
  have htMem : t.source.1 ∈
      (T.filter fun c => R c s.target.1).erase (rightBase s.target) :=
    Finset.mem_erase.mpr ⟨htExceptional,
      Finset.mem_filter.mpr ⟨t.source.2, htRelated⟩⟩
  let r0 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := ⟨s.target, ⟨s.source.1, hsMem⟩⟩
  let r1 : StatMech.FrontierA.bipartiteRightCollisionToken
      R T U rightBase := ⟨s.target, ⟨t.source.1, htMem⟩⟩
  have hr01 : r0 ≠ r1 := by
    intro h
    apply hsource
    apply Subtype.ext
    exact congrArg (fun x => x.2.1) h
  exact ⟨r0, r1, hr01⟩


theorem ownerStableSquare_twoTokenEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  dsimp only
  obtain ⟨r0, r1, hr01, l0, l1, hl01⟩ :=
    exists_ownerStableSquare_collisionTokens_and_surplusTokens
      ends m j k l zero hloop hjk hkl hk0 p hno s hstable
  let fr : Fin 2 -> StatMech.FrontierA.bipartiteRightCollisionToken
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p))
      (canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p) :=
    fun i => if i = 0 then r0 else r1
  let fl : Fin 2 -> StatMech.FrontierA.bipartiteLeftSurplusToken
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)
      (canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p) :=
    fun i => if i = 0 then l0 else l1
  have hfr : Function.Injective fr := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [fr]
  have hfl : Function.Injective fl := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [fl]
  exact ⟨⟨⟨fr, hfr⟩⟩, ⟨⟨fl, hfl⟩⟩⟩


theorem canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hσ : ∀ x, σ x ≠ x)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  dsimp only
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  let leftBase := canonicalStableRawSelfBase
    ends m j k l zero hloop hjk hkl hk0 p
  let rightBase := canonicalStableRawPreferredRightBase
    ends m j k l zero hloop hjk hkl hk0 p
  have hsourceNext (x : C) : (state x).source ≠ (state (σ x)).source := by
    intro hs
    apply (state x).exceptional
    have hsVal := congrArg Subtype.val hs
    have ha := hadvance x
    simp only [CanonicalStableRawOwnerAdvancingStep] at ha
    rw [hstep x] at hsVal
    exact hsVal.trans ha
  have hnext (x : C) : R (state x).source.1 (state (σ x)).target.1 := by
    have hsquare := canonicalStableRawExceptionalEdgeNext_square
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)
    rw [hstep x]
    exact hsquare.1
  exact StatMech.FrontierA.cycleCollisionAndSurplusTokenEmbeddings
    R T U leftBase rightBase σ
      (fun x => (state x).source) (fun x => (state x).target)
      hσ htarget hsourceNext (fun x => (state x).related) hnext
      (fun x => (state x).exceptional)


theorem canonicalClosedPreferredSelfExceptionalCycle_tokenEmbeddings
    {C : Type*} [Fintype C]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hσ : ∀ x, σ x ≠ x)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hpreferredSelf : ∀ x, (state x).target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (state x).target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (state x).target⟩) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase) ∧
      Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken
        R T leftBase) := by
  classical
  have hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) with
      hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)
          (hpreferredSelf x) hstable
      simpa only [← hstep x] using hpreferredSelf (σ x)
  exact canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep
      htarget hadvance


theorem canonicalClosedPreferredSelfExceptionalCycle_componentEmbedding
    {C : Type*} [Fintype C] (root : C)
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (σ : Equiv.Perm C)
    (state : C -> CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hstep : ∀ x, state (σ x) =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno (state x))
    (htarget : Function.Injective fun x => (state x).target)
    (hpreferredSelf : ∀ x, (state x).target.1 =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p (state x).target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p (state x).target⟩)
    (hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
    Nonempty (C ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
  have hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) with
      hadvance | hstable
    · exact hadvance
    · exfalso
      apply canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno (state x)
          (hpreferredSelf x) hstable
      simpa only [← hstep x] using hpreferredSelf (σ x)
  exact canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    root ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep
      htarget hadvance hcomponent


theorem symmDiffFold_exceptionalCycle_endpointRows_eq_empty
    {A : Type*} [Fintype A]
    (m : Finset I) (σ : Equiv.Perm A)
    (source owner : A -> ↑m -> Fin 4)
    (hadvance : ∀ x, source (σ x) = owner x) :
    symmDiffFold Finset.univ (fun x =>
      rowClass m (source x) 0 ∆ rowClass m (owner x) 0) = ∅ := by
  let R := fun x : A => rowClass m (source x) 0
  calc
    symmDiffFold Finset.univ (fun x =>
        rowClass m (source x) 0 ∆ rowClass m (owner x) 0) =
        symmDiffFold Finset.univ (fun x =>
          (∅ : Finset I) ∆ R x ∆ R (σ x)) := by
      unfold symmDiffFold
      apply Finset.fold_congr
      intro x _
      rw [show rowClass m (owner x) 0 = R (σ x) by
        simp only [R, hadvance x]]
      change R x ∆ R (σ x) = (∅ : Finset I) ∆ R x ∆ R (σ x)
      have hempty : (∅ : Finset I) ∆ R x = R x := by
        ext i
        simp [Finset.mem_symmDiff]
      rw [hempty]
    _ = symmDiffFold Finset.univ (fun _ : A => (∅ : Finset I)) :=
      symmDiffFold_endpointCancellation
        (fun _ : A => (∅ : Finset I)) R σ
    _ = ∅ := by
      rw [symmDiffFold_const]
      split <;> rfl


theorem exists_referenceTransferFold_eq_of_indexedTranslatedRows
    {A : Type*} [Fintype A]
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (source : A -> leftMaskFiber ends m j k l zero p)
    (σ : Equiv.Perm A)
    (hrows : ∀ x : A, ∃ a b : leftMaskFiber ends m j k l zero p,
      RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1) k zero ∧
        canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1 =
          canonicalTranslatedRow ends m k zero
            b.1.1 (source (σ x)).1.1) :
    ∃ a b : A -> leftMaskFiber ends m j k l zero p,
      (∀ x, RowSupportDisconnects ends m
        (canonicalTranslatedRow ends m k zero
          (a x).1.1 (source x).1.1) k zero) ∧
      (∀ x, canonicalTranslatedRow ends m k zero
          (a x).1.1 (source x).1.1 =
        canonicalTranslatedRow ends m k zero
          (b x).1.1 (source (σ x)).1.1) ∧
      symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (a x).1.1) =
        symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  choose a b hdisc heq using hrows
  refine ⟨a, b, hdisc, heq, ?_⟩
  let R := fun x : A => rowClass m (source x).1.1 0
  let TA := fun x : A =>
    canonicalTransferUnion ends m k zero (a x).1.1
  let TB := fun x : A =>
    canonicalTransferUnion ends m k zero (b x).1.1
  have hpoint : ∀ x, R x ∆ TA x = R (σ x) ∆ TB x := by
    intro x
    simpa only [R, TA, TB, canonicalTranslatedRow] using heq x
  have hfold : symmDiffFold Finset.univ (fun x => R x ∆ TA x) =
      symmDiffFold Finset.univ (fun x => R (σ x) ∆ TB x) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    intro x _
    exact hpoint x
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R] at hfold
  have hcancel {X Y Z : Finset I} (h : X ∆ Y = X ∆ Z) : Y = Z := by
    have h' := congrArg (fun K : Finset I => X ∆ K) h
    simpa [symmDiff_assoc] using h'
  exact hcancel hfold


theorem exists_canonicalStableRawExceptionalEdge_iterate_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let E := CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Fin (Fintype.card E + 1), i ≠ j ∧
      next^[i.1] s = next^[j.1] s := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let orbit : Fin (Fintype.card E + 1) → E := fun n => next^[n.1] s
  have hnotinj : ¬ Function.Injective orbit := by
    intro hinj
    have hcard := Fintype.card_le_of_injective orbit hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨i, j, hne, hij⟩


theorem exists_canonicalStableRawExceptionalEdge_target_iterate_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Fin (Fintype.card U + 1), i ≠ j ∧
      (next^[i.1] s).target = (next^[j.1] s).target := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let targets : Fin (Fintype.card U + 1) → U := fun n =>
    (next^[n.1] s).target
  have hnotinj : ¬ Function.Injective targets := by
    intro hinj
    have hcard := Fintype.card_le_of_injective targets hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  exact ⟨i, j, hne, hij⟩


theorem exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card U ∧
      (next^[i] s).target = (next^[j] s).target ∧
      ∀ a b : Nat, a < b -> b < j ->
        (next^[a] s).target ≠ (next^[b] s).target := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawCommonClosure ends m j k l zero p))
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let target : Nat -> U := fun n => (next^[n] s).target
  obtain ⟨u, v, huv, heq⟩ :=
    exists_canonicalStableRawExceptionalEdge_target_iterate_repeat
      ends m j k l zero hloop hjk hkl hk0 p hno s
  obtain ⟨i0, j0, hij0, heq0, hj0Bound⟩ :
      ∃ i0 j0 : Nat, i0 < j0 ∧ target i0 = target j0 ∧
        j0 ≤ Fintype.card U := by
    rcases lt_or_gt_of_ne huv with huv' | hvu'
    · refine ⟨u.1, v.1, huv', ?_, ?_⟩
      · simpa only [target] using heq
      · exact Nat.le_of_lt_succ v.2
    · refine ⟨v.1, u.1, hvu', ?_, ?_⟩
      · simpa only [target] using heq.symm
      · exact Nat.le_of_lt_succ u.2
  let P := fun n : Nat => ∃ i < n, target i = target n
  have hP : ∃ n, P n := ⟨j0, i0, hij0, heq0⟩
  let n := Nat.find hP
  obtain ⟨i, hin, hitarget⟩ := Nat.find_spec hP
  have hnBound : n ≤ Fintype.card U := by
    exact (Nat.find_min' hP ⟨i0, hij0, heq0⟩).trans hj0Bound
  refine ⟨i, n, hin, hnBound, hitarget, ?_⟩
  intro a b hab hbn habTarget
  have hPb : P b := ⟨a, hab, habTarget⟩
  have hnb := Nat.find_min' hP hPb
  exact (Nat.not_le_of_lt hbn) hnb


theorem exists_canonicalStableRawExceptionalEdge_minimalCycleDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card U ∧
      (next^[start] s).target = (next^[stop] s).target ∧
      (∀ a b : Nat, a < b -> b < stop ->
        (next^[a] s).target ≠ (next^[b] s).target) ∧
      ((∃ n : Nat, start ≤ n ∧ n < stop ∧
          CanonicalStableRawOwnerStableStep
            ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) ∨
        ∀ n : Nat, start ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  obtain ⟨start, stop, hlt, hstopBound, hrepeat, hdistinct⟩ :=
    exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat
      ends m j k l zero hloop hjk hkl hk0 p hno s
  refine ⟨start, stop, hlt, hstopBound, hrepeat, hdistinct, ?_⟩
  by_cases hstable : ∃ n : Nat, start ≤ n ∧ n < stop ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)
  · exact Or.inl hstable
  · right
    intro n hin hnj
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s) with
      hadvance | hownerStable
    · exact hadvance
    · exact False.elim (hstable ⟨n, hin, hnj, hownerStable⟩)


theorem canonicalMinimalClosedAdvancingCycle_tokenEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hstate :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
    (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    Nonempty (Fin (stop - start) ↪
        StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧
      Nonempty (Fin (stop - start) ↪
        StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
  classical
  dsimp only
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hdpos : 0 < stop - start := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdpos)
  let state : Fin (cycleN + 1) → E := fun x => next^[start + x.1] s
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hstep : ∀ x, state (σ x) = next (state x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [state, σ, finRotate_last, Fin.val_zero, Fin.val_last]
      calc
        next^[start] s = next^[stop] s := hstate
        _ = next^[Nat.succ (start + cycleN)] s := by congr 2 <;> omega
        _ = next (next^[start + cycleN] s) :=
          Function.iterate_succ_apply' next (start + cycleN) s
    · have hrotate : (σ x).1 = x.1 + 1 := by
        exact coe_finRotate_of_ne_last hx
      simp only [state]
      rw [hrotate]
      convert Function.iterate_succ_apply' next (start + x.1) s using 1 <;>
        omega
  have htarget : Function.Injective fun x => (state x).target := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (start + x.1) (start + y.1) (by omega)
        (by omega) (by omega)) hxy
    · exact (hdistinct (start + y.1) (start + x.1) (by omega)
        (by omega) (by omega)) hxy.symm
  have hσ : ∀ x, σ x ≠ x := by
    intro x hx
    have htargetEq : (state (σ x)).target = (state x).target := by rw [hx]
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno (state x)
    calc
      (next (state x)).target.1 = (state (σ x)).target.1 := by
        rw [hstep x]
      _ = (state x).target.1 := congrArg Subtype.val htargetEq
  have hadvanceState : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    exact hadvance (start + x.1) (by omega) (by omega)
  have htokens := canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings
    ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep
      htarget hadvanceState
  simpa only [hcycle] using htokens


theorem canonicalMinimalClosedAdvancingCycle_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hstate :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
    (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    Nonempty (Fin (stop - start) ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawExceptionalEdgeNext
                ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s)}) := by
  classical
  let E := CanonicalStableRawExceptionalEdge
    ends m j k l zero hloop hjk hkl hk0 p
  let next : E → E := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have hdpos : 0 < stop - start := by omega
  obtain ⟨cycleN, hcycle⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hdpos)
  let state : Fin (cycleN + 1) → E := fun x => next^[start + x.1] s
  let σ : Equiv.Perm (Fin (cycleN + 1)) := finRotate (cycleN + 1)
  have hstep : ∀ x, state (σ x) = next (state x) := by
    intro x
    by_cases hx : x = Fin.last cycleN
    · subst x
      simp only [state, σ, finRotate_last, Fin.val_zero, Fin.val_last]
      calc
        next^[start] s = next^[stop] s := hstate
        _ = next^[Nat.succ (start + cycleN)] s := by congr 2 <;> omega
        _ = next (next^[start + cycleN] s) :=
          Function.iterate_succ_apply' next (start + cycleN) s
    · have hrotate : (σ x).1 = x.1 + 1 :=
        coe_finRotate_of_ne_last hx
      simp only [state]
      rw [hrotate]
      convert Function.iterate_succ_apply' next (start + x.1) s using 1 <;>
        omega
  have htarget : Function.Injective fun x => (state x).target := by
    intro x y hxy
    apply Fin.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
    · exact (hdistinct (start + x.1) (start + y.1) (by omega)
        (by omega) (by omega)) hxy
    · exact (hdistinct (start + y.1) (start + x.1) (by omega)
        (by omega) (by omega)) hxy.symm
  have hadvanceState : ∀ x, CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
    intro x
    exact hadvance (start + x.1) (by omega) (by omega)
  have hcomponent : ∀ x, canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state x) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno (state 0) := by
    intro x
    have hstateIter : state x = next^[x.1] (next^[start] s) := by
      simp only [state]
      rw [Nat.add_comm start x.1]
      exact Function.iterate_add_apply next x.1 start s
    rw [hstateIter]
    exact canonicalStableRawTokenComponent_iterate
      ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s) x.1
  have hemb := canonicalClosedAdvancingExceptionalCycle_componentEmbedding
    (0 : Fin (cycleN + 1)) ends m j k l zero hloop hjk hkl hk0 p hno
      σ state hstep htarget hadvanceState hcomponent
  simpa only [hcycle, state, Fin.val_zero, Nat.add_zero] using hemb


theorem canonicalMinimalAdvancingRepeat_componentDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (((next^[start] s).source ≠ (next^[stop] s).source) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s) =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno (next^[stop] s)) ∨
      Nonempty (Fin (stop - start) ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (next^[start] s) (next^[stop] s) hrepeat with hsource | hstate
  · left
    exact ⟨hsource, canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno
        (next^[start] s) (next^[stop] s) hrepeat⟩
  · right
    exact canonicalMinimalClosedAdvancingCycle_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno s start stop
        hstartStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
        hadvance


theorem canonicalSameTargetDistinctExceptionalPair_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : s.target = t.target) (hsource : s.source ≠ t.source) :
    Nonempty (Fin 2 ↪
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
  let sInComponent :
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} := ⟨s, rfl⟩
  let tInComponent :
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨t, (canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno s t htarget).symm⟩
  have hst : sInComponent ≠ tInComponent := by
    intro h
    apply hsource
    exact congrArg (fun u => u.1.source) h
  let f : Fin 2 ->
      {u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    fun i => if i = 0 then sInComponent else tInComponent
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]


theorem canonicalMinimalAdvancingRepeat_componentEmbeddingDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    Nonempty (Fin 2 ↪
        {u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) ∨
      Nonempty (Fin (stop - start) ↪
        {token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p //
          canonicalStableRawFullLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno
                (next^[start] s)}) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalMinimalAdvancingRepeat_componentDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno s start stop
        hstartStop hrepeat hdistinct hadvance with
    ⟨hsource, _hcomponent⟩ | hleft
  · left
    exact canonicalSameTargetDistinctExceptionalPair_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno
        (next^[start] s) (next^[stop] s) hrepeat hsource
  · exact Or.inr hleft


theorem canonicalMinimalAdvancingRepeat_tokenDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop : Nat) (hstartStop : start < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hadvance : ∀ n : Nat, start ≤ n -> n < stop ->
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let T := canonicalRawCommonClosure ends m j k l zero p
    let R := CanonicalRawGateRelated ends m j k l zero p
    let U := StatMech.FrontierA.finiteRelationNeighborhood R T
    let leftBase := canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
    let rightBase := canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p
    letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) :=
      Classical.decEq _
    letI : DecidableRel R := Classical.decRel R
    (∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken
        R T U rightBase, r0 ≠ r1) ∨
      (Nonempty (Fin (stop - start) ↪
          StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧
        Nonempty (Fin (stop - start) ↪
          StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase)) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      (next^[start] s) (next^[stop] s) hrepeat with hsource | hstate
  · exact Or.inl
      (exists_two_collisionTokens_of_sameTarget_distinctSources
        ends m j k l zero hloop hjk hkl hk0 p
          (next^[start] s) (next^[stop] s) hrepeat hsource)
  · exact Or.inr
      (canonicalMinimalClosedAdvancingCycle_tokenEmbeddings
        ends m j k l zero hloop hjk hkl hk0 p hno s start stop
          hstartStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
          hadvance)


theorem ownerStableSquare_targets_isolated_in_minimalCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (start stop n : Nat) (hstartStop : start < stop)
    (hnStart : start ≤ n) (hnStop : n < stop)
    (hrepeat :
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target =
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠
      ((canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno
        ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    let succIndex := if n + 1 < stop then n + 1 else start
    ∀ q : Nat, start ≤ q -> q < stop -> q ≠ n -> q ≠ succIndex ->
      (next^[q] s).target ≠ (next^[n] s).target ∧
        (next^[q] s).target ≠ (next^[n + 1] s).target := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let target := fun a : Nat => (next^[a] s).target
  have target_ne {a b : Nat} (ha : a < stop) (hb : b < stop)
      (hab : a ≠ b) : target a ≠ target b := by
    rcases lt_or_gt_of_ne hab with hab' | hba'
    · exact hdistinct a b hab' hb
    · exact (hdistinct b a hba' ha).symm
  have hnSucc : n + 1 ≤ stop := by omega
  by_cases hnNext : n + 1 < stop
  · intro q hqStart hqStop hqn hqSucc
    have hqOld := target_ne hqStop hnStop hqn
    have hqNew := target_ne hqStop hnNext (by
      simpa only [hnNext, if_pos] using hqSucc)
    exact ⟨hqOld, hqNew⟩
  · have hnEq : n + 1 = stop := by omega
    intro q hqStart hqStop hqn hqSucc
    have hqOld := target_ne hqStop hnStop hqn
    have hqStartNe : q ≠ start := by
      simpa only [hnNext, if_neg] using hqSucc
    have hqWrap := target_ne hqStop hstartStop hqStartNe
    have hnextRepeat : target (n + 1) = target start := by
      rw [hnEq]
      exact hrepeat.symm
    exact ⟨hqOld, fun h => hqWrap (h.trans hnextRepeat)⟩


theorem canonicalSelfImageFiber_referenceTransfer_common_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (q r : leftMaskFiber ends m j k l zero p)
    (hqr : q ≠ r)
    (himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
    let hworks := (canonicalSelfTransfer_collision_oppositeWorks
      ends m j k l zero hloop hjk hkl hk0 p q r himage).1
    let alt := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r q hworks
    let self := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p q q
        (canonicalTransferWorks_self hloop hjk hkl hk0 q)
    alt ∈ canonicalMaskRightImages ends m j k l zero p q ∧
      alt ∈ canonicalMaskRightImages ends m j k l zero p r ∧
      alt ≠ self := by
  classical
  dsimp only
  let hworksRQ := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p q r himage).1
  let hworksQR := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p q r himage).2
  let alt := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r q hworksRQ
  let selfQ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p q q
      (canonicalTransferWorks_self hloop hjk hkl hk0 q)
  let selfR := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r r
      (canonicalTransferWorks_self hloop hjk hkl hk0 r)
  have haltQ : alt ∈ canonicalMaskRightImages
      ends m j k l zero p q := by
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p q alt).mpr ⟨r, hworksRQ, rfl⟩
  have htranslated : canonicalTranslatedRow ends m k zero q.1.1 q.1.1 =
      canonicalTranslatedRow ends m k zero r.1.1 r.1.1 := by
    have hrow := congrArg (fun c => rowClass m c 0) himage
    have hqrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p q q
        (canonicalTransferWorks_self hloop hjk hkl hk0 q)
    have hrrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r r
        (canonicalTransferWorks_self hloop hjk hkl hk0 r)
    exact hqrow.symm.trans (hrow.trans hrrow)
  have hopposite := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero q.1.1 r.1.1 q.1.1 r.1.1 htranslated
  have hraw : alt.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m q.1.1 k zero)
      (canonicalOuterTransfer ends m q.1.1 k zero) r.1.1 := by
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl r q q r).mpr hopposite
  have haltR : alt ∈ canonicalMaskRightImages
      ends m j k l zero p r := by
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p r alt).mpr ⟨q, hworksQR, hraw⟩
  have hselfQR : selfQ = selfR := by
    apply Subtype.ext
    apply Subtype.ext
    exact himage
  have haltNe : alt ≠ selfQ := by
    intro halt
    have hrawEq := congrArg
      (fun z : rightMaskFiber ends m j k l zero p => z.1.1)
      (halt.trans hselfQR)
    change balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) q.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) r.1.1 at hrawEq
    have hinv := congrArg (balancedSwap m
      (canonicalMiddleTransfer ends m r.1.1 k zero)
      (canonicalOuterTransfer ends m r.1.1 k zero)) hrawEq
    simp only [balancedSwap_involutive] at hinv
    apply hqr
    apply Subtype.ext
    apply Subtype.ext
    exact hinv
  exact ⟨haltQ, haltR, haltNe⟩


end StatMech.GrahamGHS.FourColor
