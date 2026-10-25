/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part63
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

theorem partialForestNonbacktrackingStep_eq_inl
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state next : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inl next) :
    next.1.1 = state.1.2 ∧ next.1.2 ≠ state.1.1 := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal hterminal => contradiction
  next continued hcontinued =>
    split at hstep
    next hback => contradiction
    next hnotBack =>
      have hnext : (⟨(state.1.2, continued),
          (hloopFree state.1.2 continued hcontinued).symm⟩ :
            PartialForestNonbacktrackingState A) = next :=
        Sum.inl.inj hstep
      rw [← hnext]
      exact ⟨rfl, hnotBack⟩

theorem partialForestNonbacktrackingStep_eq_terminal
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state : PartialForestNonbacktrackingState A) (terminal : B)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inr (Sum.inl terminal)) :
    step state.1.2 = Sum.inr terminal := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal' hterminal =>
    exact hterminal.trans (congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj hstep)))
  next continued hcontinued =>
    split at hstep <;> simp at hstep

theorem partialForestNonbacktrackingStep_eq_backtrack
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (state : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inr (Sum.inr ())) :
    step state.1.2 = Sum.inl state.1.1 := by
  classical
  unfold partialForestNonbacktrackingStep at hstep
  split at hstep
  next terminal hterminal => simp at hstep
  next continued hcontinued =>
    split at hstep
    next hback => exact hcontinued.trans (congrArg Sum.inl hback)
    next hnotBack => contradiction


theorem exists_partialForest_terminal_or_backtrack_or_longCycle
    {A B : Type*} [Fintype A] [DecidableEq A]
    (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current)
    (start : PartialForestNonbacktrackingState A) :
    ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A),
        ∃ terminal, step
          (((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start).1.2) = Sum.inr terminal) ∨
    ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A),
        step (((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[n]
            start).1.2) =
          Sum.inl (((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start).1.1)) ∨
    ∃ i j : Nat, i + 3 ≤ j ∧
      j ≤ Fintype.card (PartialForestNonbacktrackingState A) ∧
      ((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[i] start) =
        ((partialForestAdvance
          (partialForestNonbacktrackingStep step hloopFree))^[j] start) ∧
      ∀ n < j, ∃ next,
        partialForestNonbacktrackingStep step hloopFree
          ((partialForestAdvance
            (partialForestNonbacktrackingStep step hloopFree))^[n]
              start) = Sum.inl next := by
  classical
  let lifted := partialForestNonbacktrackingStep step hloopFree
  let advance := partialForestAdvance lifted
  rcases exists_partialForest_terminal_or_cycle lifted start with
    hterminal | ⟨i, j, hij, hj, hrepeat, hsteps⟩
  · obtain ⟨n, hn, terminal, hterminal⟩ := hterminal
    rcases terminal with terminal | unit
    · left
      refine ⟨n, hn, terminal, ?_⟩
      exact partialForestNonbacktrackingStep_eq_terminal
        step hloopFree (advance^[n] start) terminal hterminal
    · right
      left
      refine ⟨n, hn, ?_⟩
      exact partialForestNonbacktrackingStep_eq_backtrack
        step hloopFree (advance^[n] start) (by simpa using hterminal)
  · right
    right
    have hshift (n : Nat) (hn : n < j) :
        (advance^[n + 1] start).1.1 = (advance^[n] start).1.2 ∧
          (advance^[n + 1] start).1.2 ≠ (advance^[n] start).1.1 := by
      obtain ⟨next, hnext⟩ := hsteps n hn
      have hnextShape := partialForestNonbacktrackingStep_eq_inl
        step hloopFree (advance^[n] start) next hnext
      have hadvance : advance^[n + 1] start = next := by
        rw [show n + 1 = Nat.succ n by omega]
        rw [Function.iterate_succ_apply']
        change partialForestAdvance lifted (advance^[n] start) = next
        unfold partialForestAdvance
        rw [hnext]
      rw [hadvance]
      exact hnextShape
    have hlong : i + 3 ≤ j := by
      by_contra hnotLong
      have hshort : j = i + 1 ∨ j = i + 2 := by omega
      rcases hshort with hshort | hshort
      · have hfirst := (hshift i (by omega)).1
        apply (advance^[i] start).2
        calc
          (advance^[i] start).1.1 = (advance^[j] start).1.1 :=
            congrArg (fun state => state.1.1) hrepeat
          _ = (advance^[i] start).1.2 := by
            simpa only [hshort] using hfirst
      · have hfirst := (hshift i (by omega)).2
        have hsecond := (hshift (i + 1) (by omega)).1
        apply hfirst
        calc
          (advance^[i + 1] start).1.2 =
              (advance^[i + 2] start).1.1 := hsecond.symm
          _ = (advance^[j] start).1.1 := by rw [hshort]
          _ = (advance^[i] start).1.1 :=
            congrArg (fun state => state.1.1) hrepeat.symm
    exact ⟨i, j, hlong, hj, hrepeat, hsteps⟩

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_continuation_ne
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
    (entrance : Fin block.size) (state next : block.PostSecondState)
    (hstep : block.postSecondStep entrance state = Sum.inl next) :
    next ≠ state := by
  cases state with
  | inl outside =>
      have hnext : Sum.inr entrance = next := by
        simpa only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          Sum.inl.injEq] using hstep
      rw [← hnext]
      simp
  | inr index =>
      cases hdirect : block.directSuccessorStep index with
      | inl retained =>
          have hnext : Sum.inr retained = next := by
            simpa only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect, Sum.inl.injEq] using hstep
          rw [← hnext]
          intro heq
          apply (block.directSuccessorStep_eq_inl index retained hdirect).1
          exact Sum.inr.inj heq
      | inr terminal =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hstep

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_fresh
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
    (entrance : Fin block.size) (state : block.PostSecondState)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.postSecondStep entrance state = Sum.inr token) :
    token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  cases hstate : state with
  | inl outside =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
        hstate] at hstep
  | inr index =>
      rw [hstate] at hstep
      cases hdirect : block.directSuccessorStep index with
      | inl retained =>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hstep
      | inr fresh =>
          simp only [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect, Sum.inr.injEq] at hstep
          subst fresh
          exact (block.directSuccessorStep_eq_inr index token hdirect).2

end StatMech.GrahamGHS.FourColor
