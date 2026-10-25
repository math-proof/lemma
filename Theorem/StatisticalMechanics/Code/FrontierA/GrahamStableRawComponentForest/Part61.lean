/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part62
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

theorem CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_cycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    (∃ n ≤ block.size + 1, ∃ token,
      block.postSecondStep entrance
        ((partialForestAdvance (block.postSecondStep entrance))^[n]
          (Sum.inl ())) = Sum.inr token ∧
      token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
    ∃ i j : Nat, i < j ∧ j ≤ block.size + 1 ∧
      ((partialForestAdvance (block.postSecondStep entrance))^[i]
        (Sum.inl ())) =
      ((partialForestAdvance (block.postSecondStep entrance))^[j]
        (Sum.inl ())) ∧
      (∀ n < j, ∃ next,
        block.postSecondStep entrance
          ((partialForestAdvance (block.postSecondStep entrance))^[n]
            (Sum.inl ())) = Sum.inl next) := by
  rcases exists_partialForest_terminal_or_cycle
      (block.postSecondStep entrance) (Sum.inl ()) with
    hterminal | hcycle
  · left
    obtain ⟨n, hn, token, htoken⟩ := hterminal
    refine ⟨n, by simpa only [CanonicalStableRawComponentBalancedDirectBlock.PostSecondState,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm] using hn,
      token, htoken, ?_⟩
    let state :=
      (partialForestAdvance (block.postSecondStep entrance))^[n]
        (Sum.inl ())
    change block.postSecondStep entrance state = Sum.inr token at htoken
    obtain ⟨index, hstate⟩ : ∃ index,
        state = Sum.inr index := by
      cases hstate : state with
      | inl unit =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hstate] at htoken
      | inr index => exact ⟨index, rfl⟩
    rw [hstate] at htoken
    change (match block.directSuccessorStep index with
      | Sum.inl next => Sum.inl (Sum.inr next)
      | Sum.inr token => Sum.inr token) = Sum.inr token at htoken
    cases hdirect : block.directSuccessorStep index with
    | inl next => simp [hdirect] at htoken
    | inr fresh =>
        simp only [hdirect, Sum.inr.injEq] at htoken
        subst fresh
        exact (block.directSuccessorStep_eq_inr index token hdirect).2
  · right
    obtain ⟨i, j, hij, hj, hrepeat, hsteps⟩ := hcycle
    exact ⟨i, j, hij, by simpa only [CanonicalStableRawComponentBalancedDirectBlock.PostSecondState,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm] using hj,
      hrepeat, hsteps⟩


end StatMech.GrahamGHS.FourColor
