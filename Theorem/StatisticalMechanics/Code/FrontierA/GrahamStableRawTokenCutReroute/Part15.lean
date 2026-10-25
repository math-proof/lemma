/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part14
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawExceptionalLeftToken_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token) :
    CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) := by
  classical
  dsimp only [CanonicalStableRawStateTokenIncidence]
  refine ⟨Or.inl rfl, ?_, ?_⟩
  · exact (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase token.2.2)).2
  · exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token)


theorem canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno
            (canonicalStableRawExceptionalEdgeOfLeftToken
              ends m j k l zero hloop hjk hkl hk0 p token
                hexceptional) by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_pos hexceptional]]
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token
        (canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) s
        (canonicalStableRawExceptionalLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional) hs
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t := ⟨s, hs⟩
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno
            (Classical.choose hpredecessor) by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token
        (Classical.choose hpredecessor) s
        (Classical.choose_spec hpredecessor) hs


theorem exists_canonicalStableRawOverlapToken_in_component
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (c d : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (target : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hcd : c ≠ d)
    (hself : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c ≠
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d)
    (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
    (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
    ∃ (s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p)
      (token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p),
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token = target ∧
      (token.1 = c ∨ token.1 = d) ∧
      CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s ∧
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  have build (x y : ↑(canonicalRawCommonClosure ends m j k l zero p))
      (hxy : x ≠ y)
      (hx : CanonicalRawGateRelated ends m j k l zero p x.1 target.1)
      (hy : CanonicalRawGateRelated ends m j k l zero p y.1 target.1)
      (hxNonself : target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p x) :
      ∃ (s : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p)
        (token : CanonicalStableRawLeftSurplusToken
            ends m j k l zero hloop hjk hkl hk0 p),
        canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token = target ∧
        token.1 = x ∧
        CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token s ∧
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s := by
    let token : CanonicalStableRawLeftSurplusToken
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨x, ⟨target.1, Finset.mem_erase.mpr
        ⟨hxNonself, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩⟩⟩
    by_cases hxExceptional : x.1 ≠ canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p target
    · let s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p :=
        ⟨x, target, hx, hxExceptional⟩
      have hincidence : CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s := by
        dsimp only [CanonicalStableRawStateTokenIncidence, token, s]
        exact ⟨Or.inl rfl, hx,
          canonicalStableRawPreferredRightBase_related
            ends m j k l zero hloop hjk hkl hk0 p target⟩
      exact ⟨s, token, by apply Subtype.ext; rfl, rfl, hincidence,
        canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno token s hincidence⟩
    · have hxOwner : x.1 = canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target :=
        Classical.not_not.mp hxExceptional
      have hyExceptional : y.1 ≠ canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target := by
        intro hyOwner
        apply hxy
        apply Subtype.ext
        exact hxOwner.trans hyOwner.symm
      let s : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p :=
        ⟨y, target, hy, hyExceptional⟩
      have hincidence : CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token s := by
        dsimp only [CanonicalStableRawStateTokenIncidence, token, s]
        refine ⟨Or.inr ?_, hy, ?_⟩
        · apply Subtype.ext
          exact hxOwner
        · exact canonicalStableRawPreferredRightBase_related
            ends m j k l zero hloop hjk hkl hk0 p target
      exact ⟨s, token, by apply Subtype.ext; rfl, rfl, hincidence,
        canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno token s hincidence⟩
  by_cases hcNonself : target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p c
  · obtain ⟨s, token, htarget, hsource, hincidence, hcomponent⟩ :=
      build c d hcd hc hd hcNonself
    exact ⟨s, token, htarget, Or.inl hsource, hincidence, hcomponent⟩
  · have hcSelf : target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p c :=
      Classical.not_not.mp hcNonself
    have hdNonself : target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p d := by
      intro hdSelf
      apply hself
      exact hcSelf.symm.trans hdSelf
    obtain ⟨s, token, htarget, hsource, hincidence, hcomponent⟩ :=
      build d c hcd.symm hd hc hdNonself
    exact ⟨s, token, htarget, Or.inr hsource, hincidence, hcomponent⟩


theorem canonicalStableRawStateTokenIncidence_outputDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hincidence : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s) :
    ∃ t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      t.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p token ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s t ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s t) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let target := canonicalStableRawLeftTokenTarget
    ends m j k l zero hloop hjk hkl hk0 p token
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hsRelated : CanonicalRawGateRelated ends m j k l zero p
      s.source.1 target.1 := hincidence.2.1
  have hownerRelated : CanonicalRawGateRelated ends m j k l zero p
      owner.1 target.1 := hincidence.2.2
  have hsourceOwner : s.source ≠ owner := by
    intro h
    exact s.exceptional (congrArg Subtype.val h)
  by_cases hstable : canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p target = owner.1
  · have hexceptional : s.source.1 ≠
        canonicalStableRawPreferredRightBase
          ends m j k l zero hloop hjk hkl hk0 p target := by
      intro h
      apply hsourceOwner
      apply Subtype.ext
      exact h.trans hstable
    let t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨s.source, target, hsRelated, hexceptional⟩
    have htIncidence : CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p token t := by
      dsimp only [CanonicalStableRawStateTokenIncidence, t]
      refine ⟨?_, hsRelated, ?_⟩
      · simpa only [hstable, owner] using hincidence.1
      · simpa only [hstable] using hownerRelated
    refine ⟨t, rfl, Or.inl ⟨rfl, hstable⟩, ?_⟩
    exact canonicalStableRawStateTokenIncidence_component_eq
      ends m j k l zero hloop hjk hkl hk0 p hno token t s
        htIncidence hincidence
  · let t : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p :=
      ⟨owner, target, hownerRelated, Ne.symm hstable⟩
    have hcomponent : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s := by
      by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
          ends m j k l zero hloop hjk hkl hk0 p token
      · let u := canonicalStableRawExceptionalEdgeOfLeftToken
          ends m j k l zero hloop hjk hkl hk0 p token hexceptional
        have huIncidence : CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token u :=
          canonicalStableRawExceptionalLeftToken_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token hexceptional
        rw [canonicalStableRawTokenComponent_eq_of_target_eq
            ends m j k l zero hloop hjk hkl hk0 p hno t u (by
              apply Subtype.ext
              rfl)]
        exact canonicalStableRawStateTokenIncidence_component_eq
          ends m j k l zero hloop hjk hkl hk0 p hno token u s
            huIncidence hincidence
      · have htokenPreferred : token.1.1 =
            canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p target :=
          Classical.not_not.mp hexceptional
        have htIncidence : CanonicalStableRawStateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p token t := by
          dsimp only [CanonicalStableRawStateTokenIncidence, t]
          refine ⟨Or.inr ?_, hownerRelated, ?_⟩
          · apply Subtype.ext
            exact htokenPreferred
          · exact canonicalStableRawPreferredRightBase_related
              ends m j k l zero hloop hjk hkl hk0 p target
        exact canonicalStableRawStateTokenIncidence_component_eq
          ends m j k l zero hloop hjk hkl hk0 p hno token t s
            htIncidence hincidence
    exact ⟨t, rfl, Or.inr rfl, hcomponent⟩


theorem canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hs : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token s)
    (ht : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token t) :
    s = t ∨
      (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno t) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token ∧
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno t := by
  classical
  by_cases heq : s = t
  · exact Or.inl heq
  · right
    obtain ⟨u, huTarget, huKind, huComponent⟩ :=
      canonicalStableRawStateTokenIncidence_outputDichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno token s hs.1
    have hst : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token s t hs.1 ht.1
    rcases huKind with huStable | huAdvancing
    · exact Or.inl ⟨u, huTarget, huStable, huComponent, hst⟩
    · exact Or.inr ⟨u, huTarget, huAdvancing, huComponent, hst⟩


theorem canonicalStableRawDirectLeftToken_fullComponent
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
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawDirectLeftToken
    ends m j k l zero hloop hjk hkl hk0 p s hdirect
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token := by
    unfold token CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have ht : t = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · rfl
    · apply Subtype.ext
      rfl
  rw [show canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawFullLeftTokenComponent
      rw [dif_pos hexceptional]]
  exact congrArg (canonicalStableRawTokenComponent
    ends m j k l zero hloop hjk hkl hk0 p hno) ht


theorem canonicalStableRawSelfReroute_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawCollisionClosedLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token by
        unfold canonicalStableRawFullLeftTokenComponent
          canonicalStableRawCollisionClosedLeftTokenComponent
        rw [dif_pos hexceptional, dif_pos hexceptional]]
    exact canonicalStableRawSelfReroute_collisionClosedComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself hexceptional
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t :=
      ⟨s, canonicalStableRawSelfReroute_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hself⟩
    let chosen := Classical.choose hpredecessor
    have hchosen : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token chosen s
          (Classical.choose_spec hpredecessor)
          (canonicalStableRawSelfReroute_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p hno s hself)
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact hchosen


theorem canonicalStableRawSelfOwnerReroute_fullComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfOwnerRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfOwnerRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · let t := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p token hexceptional
    have htarget : t.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
      apply Subtype.ext
      rfl
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno t by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_pos hexceptional]]
    rw [canonicalStableRawTokenComponent_eq_of_target_eq
        ends m j k l zero hloop hjk hkl hk0 p hno t
          (canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno s) htarget]
    exact canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno s
  · have hpredecessor : ∃ t,
        CanonicalStableRawStateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p token t :=
      ⟨s, canonicalStableRawSelfOwnerReroute_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno s hself⟩
    let chosen := Classical.choose hpredecessor
    have hchosen : canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s :=
      canonicalStableRawStateTokenIncidence_component_eq
        ends m j k l zero hloop hjk hkl hk0 p hno token chosen s
          (Classical.choose_spec hpredecessor)
          (canonicalStableRawSelfOwnerReroute_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p hno s hself)
    rw [show canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno token =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno chosen by
        unfold canonicalStableRawFullLeftTokenComponent
        rw [dif_neg hexceptional, dif_pos hpredecessor]]
    exact hchosen


theorem canonicalStableRawOwnerStableSelfPair_componentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (_hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    Nonempty (Fin 2 ↪
      {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
  classical
  let sourceToken := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let ownerToken := canonicalStableRawSelfOwnerRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  have hsourceComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno sourceToken =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
    canonicalStableRawSelfReroute_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  have hownerComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno ownerToken =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s :=
    canonicalStableRawSelfOwnerReroute_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let sourceInComponent : {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨sourceToken, hsourceComponent⟩
  let ownerInComponent : {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    ⟨ownerToken, hownerComponent⟩
  have hne : sourceInComponent ≠ ownerInComponent := by
    intro heq
    apply s.exceptional
    exact congrArg (fun token => token.1.1.1) heq
  let f : Fin 2 → {token : CanonicalStableRawLeftSurplusToken
          ends m j k l zero hloop hjk hkl hk0 p //
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno token =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno s} :=
    fun i => if i = 0 then sourceInComponent else ownerInComponent
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]


end StatMech.GrahamGHS.FourColor
