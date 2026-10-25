/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part64
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

theorem CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_backtrack_or_longCycle
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
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
    let lifted := block.postSecondContinuationStep entrance
    let advance := partialForestAdvance lifted
    let start := block.postSecondInitialState entrance
    ( ∃ n ≤ Fintype.card block.PostSecondContinuationState,
        ∃ token, block.postSecondStep entrance
          (advance^[n] start).1.2 = Sum.inr token ∧
          token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
    ( ∃ n ≤ Fintype.card block.PostSecondContinuationState,
        block.postSecondStep entrance (advance^[n] start).1.2 =
          Sum.inl (advance^[n] start).1.1) ∨
    ∃ i j : Nat, i + 3 ≤ j ∧
      j ≤ Fintype.card block.PostSecondContinuationState ∧
      advance^[i] start = advance^[j] start ∧
      ∀ n < j, ∃ next, lifted (advance^[n] start) = Sum.inl next := by
  classical
  dsimp only
  rcases exists_partialForest_terminal_or_backtrack_or_longCycle
      (block.postSecondStep entrance)
      (block.postSecondStep_continuation_ne entrance)
      (block.postSecondInitialState entrance) with
    hterminal | hbacktrack | hcycle
  · left
    obtain ⟨n, hn, token, htoken⟩ := hterminal
    exact ⟨n, hn, token, htoken,
      block.postSecondStep_terminal_fresh entrance _ token htoken⟩
  · exact Or.inr (Or.inl hbacktrack)
  · exact Or.inr (Or.inr hcycle)


theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_growth_or_nonexceptional
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
    (entrance : Fin block.size) (state : block.PostSecondState)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.postSecondStep entrance state = Sum.inr token) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨index, hstate⟩ : ∃ index, state = Sum.inr index := by
    cases hstate : state with
    | inl outside =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hstate] at hstep
    | inr index => exact ⟨index, rfl⟩
  rw [hstate] at hstep
  cases hdirect : block.directSuccessorStep index with
  | inl retained =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hdirect] at hstep
  | inr fresh =>
      simp only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hdirect, Sum.inr.injEq] at hstep
      subst fresh
      have hdata := block.directSuccessorStep_eq_inr index token hdirect
      have htoken := hdata.1
      have hfresh := hdata.2
      cases hforest : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (block.sourceBlock index) with
      | inr terminal => exact Or.inr ⟨terminal⟩
      | inl direct =>
          left
          have hforestToken := canonicalStableRawComponentForestStep_token
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock index)
          rw [hforest] at hforestToken
          have hdirectFresh : ∀ q, direct ≠ block.directs q := by
            intro q heq
            apply hfresh
            apply Finset.mem_map.mpr
            refine ⟨q, Finset.mem_univ _, ?_⟩
            calc
              block.tokenBlock q =
                  canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      (block.directs q) := rfl
              _ = canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      direct := congrArg _ heq.symm
              _ = canonicalStableRawComponentSuccessorToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      (block.sourceBlock index) := hforestToken
              _ = token := htoken.symm
          obtain ⟨directs, _hprefix, _hlast⟩ :=
            finiteEmbedding_snoc block.size block.directs direct hdirectFresh
          let tokens : Fin (block.size + 1) ↪
              CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component :=
            directs.trans (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
          exact ⟨⟨block.size + 1, by omega, directs, tokens⟩, rfl⟩


end StatMech.GrahamGHS.FourColor
