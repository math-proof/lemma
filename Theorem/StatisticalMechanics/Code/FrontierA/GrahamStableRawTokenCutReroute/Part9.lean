/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
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
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfOwnerRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself) := by
  classical
  intro hexceptional
  apply hexceptional
  have howner := hstable.2
  unfold canonicalStableRawSelfOwnerRerouteLeftToken
  simpa only [canonicalStableRawLeftTokenTarget] using howner.symm


theorem canonicalStableRawSelfReroute_eq_directToken_dichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s t : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (tdirect : t.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p t.source)
    (htoken : canonicalStableRawSelfRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s hself =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t tdirect) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (t = next s ∧ CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) ∨
      (CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno s ∧
        t.source = s.source ∧ t.target = (next s).target ∧
        t ≠ next s) := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  unfold canonicalStableRawSelfRerouteLeftToken
    canonicalStableRawDirectLeftToken at htoken
  have hsource : t.source = s.source := by
    exact (congrArg Sigma.fst htoken).symm
  have htarget : t.target = (next s).target := by
    apply Subtype.ext
    exact (congrArg (fun token => token.2.1) htoken).symm
  rcases canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
      ends m j k l zero hloop hjk hkl hk0 p hno s with
    hadvance | ⟨hnextSource, hnextOwner⟩
  · right
    refine ⟨congrArg Subtype.val hadvance, hsource, htarget, ?_⟩
    intro ht
    apply s.exceptional
    have hsources := congrArg
      (fun state : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p => state.source.1) ht
    exact (congrArg Subtype.val hsource).symm.trans
      (hsources.trans (congrArg Subtype.val hadvance))
  · left
    have ht : t = next s :=
      canonicalStableRawExceptionalEdge_eq_of_source_target_eq
        (hsource.trans hnextSource.symm) htarget
    refine ⟨ht, ?_⟩
    exact ⟨hnextSource, hnextOwner⟩


theorem canonicalStableRawSelfReroute_componentDichotomy
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
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    let token := canonicalStableRawSelfRerouteLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno s hself
    let component := StatMech.FrontierA.functionWeakComponent next
    ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token ∨
      canonicalStableRawLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token = component s ∨
      ∃ t : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno s ∧
          t.source = s.source ∧ t.target = (next s).target ∧
          t ≠ next s ∧
          canonicalStableRawLeftTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno token =
            component t := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let component := StatMech.FrontierA.functionWeakComponent next
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · let t := canonicalStableRawExceptionalEdgeOfLeftToken
      ends m j k l zero hloop hjk hkl hk0 p token hexceptional
    have tdirect : t.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p t.source := by
      exact Finset.ne_of_mem_erase token.2.2
    have htokenDirect : token = canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p t tdirect := by
      apply Sigma.ext rfl
      rfl
    have htag : canonicalStableRawLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno token =
        component t := by
      simp only [canonicalStableRawLeftTokenComponent, hexceptional,
        dite_true]
      apply congrArg component
      apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
      · rfl
      · rfl
    rcases canonicalStableRawSelfReroute_eq_directToken_dichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno s t hself tdirect
          htokenDirect with ⟨ht, hstable⟩ | ⟨hadvance, hsource, htarget,
            htne⟩
    · right
      left
      rw [htag, ht]
      exact StatMech.FrontierA.functionWeakComponent_next next s
    · right
      right
      exact ⟨t, hadvance, hsource, htarget, htne, htag⟩
  · exact Or.inl hexceptional


end StatMech.GrahamGHS.FourColor
