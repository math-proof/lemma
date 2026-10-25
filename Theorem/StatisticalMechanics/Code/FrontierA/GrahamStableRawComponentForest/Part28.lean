/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part28
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

theorem canonicalStableRawComponentReferenceStepBelowRank_card_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (rankBound : Nat) :
    Nat.card (CanonicalStableRawComponentSelfBelowRank
        ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) ≤
      Nat.card (CanonicalStableRawComponentDirectBelowRank
          ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) +
        Nat.card (CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hcard := Nat.card_le_card_of_injective
    (canonicalStableRawComponentReferenceStepBelowRankEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component rankBound)
    (canonicalStableRawComponentReferenceStepBelowRankEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        rankBound).injective
  simpa only [Nat.card_sum] using hcard


theorem canonicalStableRawComponentCrossCollision_source_eq_direct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.1.1.source = collision.1.2.1.source := by
  have hclassification :=
    canonicalStableRawComponentCrossCollision_classification
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  rcases hclassification.2.2 with
    ⟨hdirect, hstable⟩ | ⟨_, hsource, _, _⟩
  · rw [hdirect, hstable.1]
  · exact hsource.symm


theorem canonicalStableRawComponentResidualCollision_ranked_sameTarget
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
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.1.1.2.1.target = collision.1.2.1.target ∧
      canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.2.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.2.1.source := by
  constructor
  · exact (canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component collision).symm
  · let self := collision.1.1.1.1.1.1
    have hlower : collision.1.1.1.2.1.source =
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2).1 := by
      apply Subtype.ext
      exact canonicalStableRawComponentReferenceOwner_directOccupant_source
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1
    have hupper : collision.1.2.1.source = self.1.source :=
      canonicalStableRawComponentReferenceSource_directCollision_source
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
    rw [hlower, hupper]
    exact canonicalStableRawReferenceOwnerLeftToken_rank_lt
      ends m j k l zero hloop hjk hkl hk0 p self.1 self.2.2


theorem canonicalStableRawComponentResidualLower_fresh_or_rightCollision
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
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let lower := collision.1.1.1.2
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧
        ∀ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ≠ canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component continuation =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨lower.1, lower.2.1⟩ := by
  classical
  dsimp only
  let lower := collision.1.1.1.2
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨lower.1, lower.2.1⟩ with
  | inl continuation =>
      right
      refine ⟨continuation, rfl, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨lower.1, lower.2.1⟩
      rw [hstep] at htoken
      exact htoken
  | inr terminal =>
      left
      refine ⟨terminal, rfl, ?_⟩
      intro direct
      exact canonicalStableRawComponentNonexceptionalToken_ne_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component terminal direct


end StatMech.GrahamGHS.FourColor
