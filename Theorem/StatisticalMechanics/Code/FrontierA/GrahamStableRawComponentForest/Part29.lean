/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part7
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

theorem canonicalStableRawComponentResidualLower_rightCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ =
        Sum.inl continuation) :
    ∃ third : CanonicalStableRawComponentSecondAlternateDirectCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      third.1.1 = collision.1.1 ∧ third.1.2 = continuation := by
  let lower := collision.1.1.1.2
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨lower.1, lower.2.1⟩
  rw [hstep] at htoken
  have halternate : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩ := by
    apply Subtype.ext
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          lower.1 lower.2.2 =
      (canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩).1
    unfold canonicalStableRawComponentSuccessorToken
    rw [dif_neg lower.2.2]
  let third : CanonicalStableRawComponentSecondAlternateDirectCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨(collision.1.1, continuation), halternate.trans htoken.symm⟩
  exact ⟨third, rfl, rfl⟩


theorem canonicalStableRawComponentResidualLower_continuation_source_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ =
        Sum.inl continuation) :
    let lower := collision.1.1.1.2
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno lower.1
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p lower.1.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p lower.1.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧
        continuation.1.source = owner) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧
        continuation.1.source = lower.1.source ∧
        canonicalStableRawSourceRank ends m j k l zero p
            continuation.1.source =
          canonicalStableRawSourceRank ends m j k l zero p lower.1.source) := by
  classical
  dsimp only
  let lower := collision.1.1.1.2
  have htoken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨lower.1, lower.2.1⟩
  rw [hstep] at htoken
  have hsource : continuation.1.source =
      (canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          lower.1 lower.2.2).1 := by
    apply Subtype.ext
    have hraw := congrArg
      (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1.1)
      htoken
    simpa only [canonicalStableRawComponentDirectEmbedding_apply,
      canonicalStableRawStateLeftToken, dif_neg continuation.2.2,
      canonicalStableRawComponentSuccessorToken, dif_neg lower.2.2] using hraw
  rcases canonicalStableRawDirectAlternateLeftToken_source_split
      ends m j k l zero hloop hjk hkl hk0 p hno lower.1 lower.2.2 with
    howner | hsame
  · exact Or.inl ⟨howner.1, hsource.trans howner.2⟩
  · exact Or.inr ⟨hsame.1, hsource.trans hsame.2,
      congrArg (canonicalStableRawSourceRank ends m j k l zero p)
        (hsource.trans hsame.2)⟩


end StatMech.GrahamGHS.FourColor
