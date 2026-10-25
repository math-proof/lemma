/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part19
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

theorem canonicalStableRawComponentExceptionalSuccessorDirect_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1) :
    canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (canonicalStableRawComponentExceptionalSuccessorDirect
            ends m j k l zero hloop hjk hkl hk0 p hno component
              s hexceptional) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  have hinverse :=
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
        ⟨canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s,
          hexceptional⟩
  exact congrArg Subtype.val hinverse


theorem canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩).1) :
    let recovered := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    recovered.1 = next ∨
      (recovered.1.source ≠ next.source ∧ recovered.1.target = next.target) := by
  classical
  dsimp only
  let recovered := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨direct.1, direct.2.1⟩ hexceptional
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1
  have hexceptionalRaw : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno
            direct.1 direct.2.2) := by
    simpa only [canonicalStableRawComponentSuccessorToken,
      dif_neg direct.2.2] using hexceptional
  have hnextTarget :=
    canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next
      ends m j k l zero hloop hjk hkl hk0 p hno
        direct.1 direct.2.2 hexceptionalRaw
  have htoken := congrArg Subtype.val
    (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional)
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno recovered.1 =
    (canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩).1 at htoken
  unfold canonicalStableRawStateLeftToken
    canonicalStableRawComponentSuccessorToken at htoken
  rw [dif_neg recovered.2.2, dif_neg direct.2.2] at htoken
  have htarget : recovered.1.target = next.target := by
    apply Subtype.ext
    have htokenTarget := congrArg (fun token => token.2.1) htoken
    have hnextTargetValue := congrArg Subtype.val hnextTarget
    change (canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        direct.1 direct.2.2).2.1 = next.target.1 at hnextTargetValue
    exact htokenTarget.trans hnextTargetValue
  rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
      recovered.1 next htarget with hsource | heq
  · exact Or.inr ⟨hsource, htarget⟩
  · exact Or.inl heq


theorem canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
    (canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩ hexceptional).1 =
      canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
  classical
  dsimp only
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨self.1, self.2.1⟩
      (canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing)
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  have htoken := congrArg Subtype.val
    (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩
        (canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
          ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing))
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1 =
    (canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩).1 at htoken
  unfold canonicalStableRawStateLeftToken
    canonicalStableRawComponentSuccessorToken at htoken
  rw [dif_neg direct.2.2, dif_pos self.2.2] at htoken
  have hsource : direct.1.source = next.source := by
    apply Subtype.ext
    have howner := congrArg (fun token => token.1.1) htoken
    change direct.1.source.1 = canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p self.1.target at howner
    exact howner.trans hadvancing.symm
  have htarget : direct.1.target = next.target := by
    apply Subtype.ext
    have htargetValue := congrArg (fun token => token.2.1) htoken
    change direct.1.target.1 = next.target.1 at htargetValue
    exact htargetValue
  exact canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    hsource htarget


theorem canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawComponentExceptionalSuccessorDirect
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ hexceptional).1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
  dsimp only
  rw [canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing
    ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing]
  exact canonicalStableRawOwnerAdvancingStep_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2 hadvancing


end StatMech.GrahamGHS.FourColor
