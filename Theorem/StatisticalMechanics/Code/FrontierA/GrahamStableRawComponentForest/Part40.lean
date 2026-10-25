/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part40
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

theorem canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↔
      Nat.card (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
        Nat.card (CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let exceptional := fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component =>
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1
  have hstate := Nat.card_congr
    (canonicalStableRawComponentStateEquivSelfSumDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hdirect := Nat.card_congr
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  have htoken := (Nat.card_congr (Equiv.sumCompl exceptional)).symm
  simp only [Nat.card_sum] at hstate htoken
  change _ = Nat.card (CanonicalStableRawComponentExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) +
    Nat.card (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) at htoken
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  omega


theorem canonicalStableRawTokenComponent_embedding_of_direct_card_le_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdirectSelf : Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Terminal := CanonicalStableRawComponentNonexceptionalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have hdirectSelf' : Nat.card Direct ≤ Nat.card Self := by
    simpa only [Direct, Self] using hdirectSelf
  have hpair : 2 * Nat.card Self ≤ Nat.card Token :=
    canonicalStableRawComponent_two_mul_self_card_le_token
      ends m j k l zero hloop hjk hkl hk0 p hno component
  have htoken : Nat.card Direct + Nat.card Terminal = Nat.card Token := by
    simpa only [Nat.card_sum] using Nat.card_congr
      (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
        ends m j k l zero hloop hjk hkl hk0 p hno component)
  have hselfTerminal : Nat.card Self ≤ Nat.card Terminal := by
    omega
  apply Function.Embedding.nonempty_of_card_le
  exact (canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    ends m j k l zero hloop hjk hkl hk0 p hno component).2 hselfTerminal


theorem canonicalStableRawComponent_direct_card_gt_self_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) <
      Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  by_contra hnot
  have hdirectSelf : Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ≤
      Nat.card (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Nat.le_of_not_gt hnot
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_direct_card_le_self
      ends m j k l zero hloop hjk hkl hk0 p hno component hdirectSelf
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective embedding embedding.injective)) hdeficit


theorem canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (forest : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ↪
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  apply Function.Embedding.nonempty_of_card_le
  apply (canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional
    ends m j k l zero hloop hjk hkl hk0 p hno component).2
  exact Nat.card_le_card_of_injective forest forest.injective


theorem canonicalStableRawTokenComponent_embedding_of_terminalClosureHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.card ≤ (canonicalStableRawComponentTerminalNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨matching, _⟩ :=
    FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
      (canonicalStableRawComponentTerminalSystem
        ends m j k l zero hloop hjk hkl hk0 p hno component) (by
          intro sources
          simpa only [canonicalStableRawComponentTerminalNeighborhood] using
            hhall sources)
  exact canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component matching


theorem canonicalStableRawTokenComponent_embedding_of_referenceTerminalHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.card ≤
        (canonicalStableRawComponentReferenceTerminalNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources).card) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨matching, _⟩ :=
    FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall
      (canonicalStableRawComponentReferenceTerminalSystem
        ends m j k l zero hloop hjk hkl hk0 p hno component) (by
          intro sources
          simpa only [canonicalStableRawComponentReferenceTerminalNeighborhood]
            using hhall sources)
  exact canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component matching


end StatMech.GrahamGHS.FourColor
