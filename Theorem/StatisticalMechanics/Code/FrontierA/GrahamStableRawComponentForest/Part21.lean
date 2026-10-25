/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part21
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

theorem canonicalStableRawComponentDirectForestAdvance_eq_of_step
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
    canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        continuation := by
  change canonicalStableRawComponentDirectForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component direct =
    Sum.inl continuation at hstep
  unfold canonicalStableRawComponentDirectForestAdvance partialForestAdvance
  rw [hstep]


theorem exists_canonicalStableRawComponentDirect_terminal_or_cycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ startIndex stopIndex : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        ∀ n < stopIndex, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              (advance^[n] start).1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Direct := Fintype.ofFinite Direct
  let step := canonicalStableRawComponentDirectForestStep
    ends m j k l zero hloop hjk hkl hk0 p hno component
  have horbit := exists_partialForest_terminal_or_cycle step start
  have hadvanceEq : partialForestAdvance step =
      canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
    rfl
  rw [hadvanceEq] at horbit
  unfold step canonicalStableRawComponentDirectForestStep at horbit
  change _ ∨ ∃ startIndex stopIndex : Nat, _ at horbit
  rcases horbit with hterminal |
    ⟨startIndex, stopIndex, hlt, hstop, heq, hsteps⟩
  · exact Or.inl (by
      simpa only [Nat.card_eq_fintype_card] using hterminal)
  · right
    refine ⟨startIndex, stopIndex, hlt, ?_, heq, ?_⟩
    · simpa only [Nat.card_eq_fintype_card] using hstop
    intro n hn
    obtain ⟨continuation, hcontinuation⟩ := hsteps n hn
    refine ⟨continuation, hcontinuation, ?_⟩
    exact canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start)
        continuation hcontinuation


theorem
    exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      (∃ n < Nat.card Direct, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)) ∨
      ∃ startIndex stopIndex : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        ∀ n < stopIndex, ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
              Sum.inl continuation ∧
            rank (advance^[n] start) ≤ rank continuation ∧
            let next := canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno
                (advance^[n] start).1
            continuation.1 = next ∨
              (continuation.1.source ≠ next.source ∧
                continuation.1.target = next.target) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  rcases exists_canonicalStableRawComponentDirect_terminal_or_cycle
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal |
      ⟨startIndex, stopIndex, hlt, hstop, hrepeat, hsteps⟩
  · exact Or.inl hterminal
  · right
    by_cases hdrop : ∃ n < stopIndex, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)
    · left
      obtain ⟨n, hn, continuation, hstep, hrank⟩ := hdrop
      exact ⟨n, by omega, continuation, hstep, hrank⟩
    · right
      refine ⟨startIndex, stopIndex, hlt, hstop, hrepeat, ?_⟩
      intro n hn
      obtain ⟨continuation, hstep, hkind⟩ := hsteps n hn
      refine ⟨continuation, hstep, ?_, hkind⟩
      have hnotlt : ¬ rank continuation < rank (advance^[n] start) := by
        intro hrank
        exact hdrop ⟨n, hn, continuation, hstep, hrank⟩
      exact Nat.le_of_not_gt hnotlt


theorem canonicalStableRawComponentDirectSibling_componentPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (next : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hsource : continuation.1.source ≠ next.source)
    (htarget : continuation.1.target = next.target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  simpa only [continuation.2.1] using
    (canonicalSameTargetDistinctExceptionalPair_componentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno
        continuation.1 next htarget hsource)


theorem canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : Fin 2 → CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
    if i = 0 then directMap first else directMap second
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]


theorem canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let f : Fin 2 → CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
    if i = 0 then first else second
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [f]


theorem canonicalStableRawComponentDirectSibling_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsibling : continuation.1.source ≠
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧
      continuation.1.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg Subtype.val hsibling.2.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne


theorem canonicalStableRawComponentDirectSibling_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsibling : continuation.1.source ≠
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧
      continuation.1.target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg Subtype.val hsibling.2.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne


theorem canonicalStableRawComponentDirectNext_twoTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg
            (fun edge => edge.target.1) hnext.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne


theorem canonicalStableRawComponentDirectNext_twoDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  have hne : direct ≠ continuation := by
    intro heq
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    calc
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target.1 =
          continuation.1.target.1 := congrArg
            (fun edge => edge.target.1) hnext.symm
      _ = direct.1.target.1 := congrArg
        (fun state => state.1.target.1) heq.symm
  exact canonicalStableRawComponentDistinctDirect_twoDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
      direct continuation hne


theorem canonicalStableRawComponentDirectCycle_sibling_or_allNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat)
    (hsteps : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target)) :
    (∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1.source ≠ next.source ∧
            continuation.1.target = next.target) ∨
      ∀ n, startIndex ≤ n -> n < stopIndex ->
        ∃ continuation : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).1,
                  ((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).2.1⟩ = Sum.inl continuation ∧
            continuation.1 = canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno
                ((canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1 := by
  classical
  by_cases hsibling : ∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1
          continuation.1.source ≠ next.source ∧
            continuation.1.target = next.target
  · exact Or.inl hsibling
  · right
    intro n hnStart hnStop
    obtain ⟨continuation, hstep, hkind⟩ := hsteps n hnStart hnStop
    refine ⟨continuation, hstep, ?_⟩
    rcases hkind with hnext | hsib
    · exact hnext
    · exact False.elim (hsibling ⟨n, hnStart, hnStop,
        continuation, hstep, hsib⟩)


theorem
    canonicalStableRawComponentDirectAllNext_stableTokens_or_allAdvancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat)
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    (∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        CanonicalStableRawOwnerStableStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1 ∧
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).1,
                  ((canonicalStableRawComponentDirectForestAdvance
                      ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                    start).2.1⟩ = Sum.inl continuation ∧
          continuation.1 = canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno
              ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                start).1 ∧
          Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      ∀ n, startIndex ≤ n -> n < stopIndex ->
        CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1 := by
  classical
  by_cases hstable : ∃ n, startIndex ≤ n ∧ n < stopIndex ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
            start).1
  · left
    obtain ⟨n, hnStart, hnStop, hownerStable⟩ := hstable
    obtain ⟨continuation, hstep, hnext⟩ := hallNext n hnStart hnStop
    refine ⟨n, hnStart, hnStop, continuation, hownerStable,
      hstep, hnext, ?_⟩
    exact canonicalStableRawComponentDirectNext_twoTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start)
        continuation hnext
  · right
    intro n hnStart hnStop
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          ((canonicalStableRawComponentDirectForestAdvance
            ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
            start).1 with hadvancing | hownerStable
    · exact hadvancing
    · exact False.elim (hstable ⟨n, hnStart, hnStop, hownerStable⟩)


theorem canonicalStableRawComponentDirectAllNext_project
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex n : Nat)
    (hn : n ≤ stopIndex - startIndex)
    (hallNext : ∀ q, startIndex ≤ q -> q < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[q]
              start).1) :
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (advance^[startIndex + n] start).1 =
      (next^[n] (advance^[startIndex] start).1) := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  have hlocal (q : Nat) (hq : q < n) :
      (advance ((advance^[q]) base)).1 = next ((advance^[q]) base).1 := by
    have hindex : startIndex + q < stopIndex := by omega
    obtain ⟨continuation, hforest, hcontinuation⟩ :=
      hallNext (startIndex + q) (by omega) hindex
    have hglobal : (advance^[q]) base =
        advance^[startIndex + q] start := by
      unfold base
      rw [Nat.add_comm startIndex q]
      exact (Function.iterate_add_apply advance q startIndex start).symm
    have hforestLocal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨((advance^[q]) base).1, ((advance^[q]) base).2.1⟩ =
        Sum.inl continuation := by
      rw [hglobal]
      exact hforest
    have hadvance : advance ((advance^[q]) base) = continuation :=
      canonicalStableRawComponentDirectForestAdvance_eq_of_step
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ((advance^[q]) base) continuation hforestLocal
    calc
      (advance ((advance^[q]) base)).1 = continuation.1 :=
        congrArg Subtype.val hadvance
      _ = next ((advance^[q]) base).1 := by
        rw [hglobal]
        exact hcontinuation
  have hproject := map_iterate_eq_of_step_until
    advance next (fun direct => direct.1) base n hlocal
  have hglobal : advance^[n] base = advance^[startIndex + n] start := by
    unfold base
    rw [Nat.add_comm startIndex n]
    exact (Function.iterate_add_apply advance n startIndex start).symm
  rw [hglobal] at hproject
  exact hproject


theorem canonicalStableRawComponentDirectAllNext_intervalEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex first stop : Nat)
    (hfirstStop : first < stop)
    (hstopLength : stop ≤ stopIndex - startIndex)
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1)
    (hdistinct : ∀ a b : Nat, a < b -> b < stop ->
      ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[a]
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
          start).1).target ≠
      ((canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno)^[b]
        ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
          start).1).target) :
    Nonempty (Fin (stop - first) ↪
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  let f : Fin (stop - first) → Direct := fun i =>
    advance^[startIndex + (first + i.1)] start
  have hproject (n : Nat) (hn : n ≤ stopIndex - startIndex) :
      (advance^[startIndex + n] start).1 = next^[n] base.1 := by
    exact canonicalStableRawComponentDirectAllNext_project
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex n hn hallNext
  refine ⟨⟨f, ?_⟩⟩
  intro x y hxy
  apply Fin.ext
  by_contra hval
  rcases lt_or_gt_of_ne hval with hxyVal | hyxVal
  · have hxStop : first + x.1 < stop := by omega
    have hyStop : first + y.1 < stop := by omega
    have hxProject := hproject (first + x.1) (by omega)
    have hyProject := hproject (first + y.1) (by omega)
    apply hdistinct (first + x.1) (first + y.1) (by omega) hyStop
    calc
      (next^[first + x.1] base.1).target = (f x).1.target := by
        exact congrArg (fun edge => edge.target) hxProject.symm
      _ = (f y).1.target := congrArg (fun direct => direct.1.target) hxy
      _ = (next^[first + y.1] base.1).target := by
        exact congrArg (fun edge => edge.target) hyProject
  · have hxStop : first + x.1 < stop := by omega
    have hyStop : first + y.1 < stop := by omega
    have hxProject := hproject (first + x.1) (by omega)
    have hyProject := hproject (first + y.1) (by omega)
    apply hdistinct (first + y.1) (first + x.1) (by omega) hxStop
    calc
      (next^[first + y.1] base.1).target = (f y).1.target := by
        exact congrArg (fun edge => edge.target) hyProject.symm
      _ = (f x).1.target := congrArg (fun direct => direct.1.target) hxy.symm
      _ = (next^[first + x.1] base.1).target := by
        exact congrArg (fun edge => edge.target) hxProject


theorem canonicalStableRawClosedNextCycle_of_directCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
                ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (next^[stopIndex - startIndex] (advance^[startIndex] start).1) =
      (advance^[startIndex] start).1 := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  have hlocal (n : Nat) (hn : n < stopIndex - startIndex) :
      ((advance^[n + 1]) base).1 = next ((advance^[n]) base).1 := by
    have hindex : startIndex + n < stopIndex := by omega
    obtain ⟨continuation, hforest, hcontinuation⟩ :=
      hallNext (startIndex + n) (by omega) hindex
    have hglobal : (advance^[n]) base =
        advance^[startIndex + n] start := by
      unfold base
      rw [Nat.add_comm startIndex n]
      exact (Function.iterate_add_apply advance n startIndex start).symm
    have hforestLocal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨((advance^[n]) base).1, ((advance^[n]) base).2.1⟩ =
        Sum.inl continuation := by
      rw [hglobal]
      exact hforest
    have hadvance : advance ((advance^[n]) base) = continuation := by
      exact canonicalStableRawComponentDirectForestAdvance_eq_of_step
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ((advance^[n]) base) continuation hforestLocal
    calc
      ((advance^[n + 1]) base).1 =
          (advance ((advance^[n]) base)).1 := by
            rw [Function.iterate_succ_apply']
      _ = continuation.1 := congrArg Subtype.val hadvance
      _ = next ((advance^[n]) base).1 := by
        rw [hglobal]
        exact hcontinuation
  have hproject := map_iterate_eq_of_step_until
    advance next (fun direct => direct.1) base (stopIndex - startIndex)
      (fun n hn => by
        simpa only [Function.iterate_succ_apply'] using hlocal n hn)
  have hend : advance^[stopIndex - startIndex] base =
      advance^[stopIndex] start := by
    calc
      advance^[stopIndex - startIndex] base =
          advance^[stopIndex - startIndex] (advance^[startIndex] start) := rfl
      _ = advance^[(stopIndex - startIndex) + startIndex] start :=
        (Function.iterate_add_apply advance (stopIndex - startIndex)
          startIndex start).symm
      _ = advance^[stopIndex] start := by congr 2 <;> omega
  rw [hend, ← hrepeat] at hproject
  exact hproject.symm


theorem canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      let advance := canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
      let base := advance^[startIndex] start
      ∃ first stop : Nat, first < stop ∧
        stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ n : Nat, first ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[n] base.1)) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  dsimp only
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  let length := stopIndex - startIndex
  have hlength : 0 < length := by omega
  have hclosed : next^[length] base.1 = base.1 := by
    exact canonicalStableRawClosedNextCycle_of_directCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex hlt hrepeat hallNext
  obtain ⟨first, stop, hfirstStop, hstopLength, htarget, hdistinct⟩ :=
    exists_minimal_iterateKey_repeat_of_closedOrbit
      next (fun edge => edge.target) base.1 length hlength hclosed
  have hproject (n : Nat) (hn : n ≤ length) :
      (advance^[startIndex + n] start).1 = next^[n] base.1 := by
    exact canonicalStableRawComponentDirectAllNext_project
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex n hn hallNext
  by_cases hstable : ∃ n, first ≤ n ∧ n < stop ∧
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] base.1)
  · left
    obtain ⟨n, hnFirst, hnStop, hownerStable⟩ := hstable
    have hnLength : n < length := hnStop.trans_le hstopLength
    obtain ⟨continuation, hstep, hnext⟩ :=
      hallNext (startIndex + n) (by omega) (by omega)
    exact canonicalStableRawComponentDirectNext_twoTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (advance^[startIndex + n] start) continuation hnext
  · have hadvancing : ∀ n : Nat, first ≤ n -> n < stop ->
        CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno
            (next^[n] base.1) := by
      intro n hnFirst hnStop
      rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
          ends m j k l zero hloop hjk hkl hk0 p hno
            (next^[n] base.1) with hadvancing | hownerStable
      · exact hadvancing
      · exact False.elim
          (hstable ⟨n, hnFirst, hnStop, hownerStable⟩)
    rcases canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq
        (next^[first] base.1) (next^[stop] base.1) htarget with
      hsource | hstate
    · left
      let firstDirect := advance^[startIndex + first] start
      let stopDirect := advance^[startIndex + stop] start
      have hfirstProject : firstDirect.1 = next^[first] base.1 :=
        hproject first (by omega)
      have hstopProject : stopDirect.1 = next^[stop] base.1 :=
        hproject stop hstopLength
      have hne : firstDirect ≠ stopDirect := by
        intro heq
        apply hsource
        calc
          (next^[first] base.1).source = firstDirect.1.source :=
            congrArg (fun edge => edge.source) hfirstProject.symm
          _ = stopDirect.1.source := congrArg
            (fun direct => direct.1.source) heq
          _ = (next^[stop] base.1).source :=
            congrArg (fun edge => edge.source) hstopProject
      exact canonicalStableRawComponentDistinctDirect_twoTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
          firstDirect stopDirect hne
    · right
      refine ⟨first, stop, hfirstStop, hstopLength, hstate,
        hdistinct, hadvancing, ?_⟩
      let firstDirect := advance^[startIndex + first] start
      have hfirstProject : firstDirect.1 = next^[first] base.1 :=
        hproject first (by omega)
      have hcomponent : canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[first] base.1) = component := by
        rw [← hfirstProject]
        exact firstDirect.2.1
      have hemb := canonicalMinimalClosedAdvancingCycle_componentEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno base.1 first stop
          hfirstStop hstate (fun a b _ hab hb => hdistinct a b hab hb)
          hadvancing
      rw [hcomponent] at hemb
      exact hemb


theorem canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (startIndex stopIndex : Nat) (hlt : startIndex < stopIndex)
    (hrepeat :
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex]
        start) =
      ((canonicalStableRawComponentDirectForestAdvance
          ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex]
        start))
    (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex ->
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).1,
                ((canonicalStableRawComponentDirectForestAdvance
                    ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
                  start).2.1⟩ = Sum.inl continuation ∧
        continuation.1 = canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno
            ((canonicalStableRawComponentDirectForestAdvance
              ends m j k l zero hloop hjk hkl hk0 p hno component)^[n]
              start).1) :
    (Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      let advance := canonicalStableRawComponentDirectForestAdvance
        ends m j k l zero hloop hjk hkl hk0 p hno component
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno
      let base := advance^[startIndex] start
      ∃ first stop : Nat, first < stop ∧
        stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ n : Nat, first ≤ n -> n < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[n] base.1)) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (stop - first) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  let base := advance^[startIndex] start
  obtain ⟨continuation, hstep, hnext⟩ :=
    hallNext startIndex (Nat.le_refl _) hlt
  have hdirectPair : Nonempty (Fin 2 ↪
      CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    canonicalStableRawComponentDirectNext_twoDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (advance^[startIndex] start) continuation hnext
  rcases canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex hlt hrepeat hallNext with
    htokenPair | hcycle
  · exact Or.inl ⟨hdirectPair, htokenPair⟩
  · right
    dsimp only at hcycle ⊢
    obtain ⟨first, stop, hfirstStop, hstopLength, hstate,
      hdistinct, hadvancing, htokens⟩ := hcycle
    refine ⟨first, stop, hfirstStop, hstopLength, hstate,
      hdistinct, hadvancing, ?_, htokens⟩
    exact canonicalStableRawComponentDirectAllNext_intervalEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
        start startIndex stopIndex first stop hfirstStop hstopLength
          hallNext hdistinct


theorem
    exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let rank := fun direct : Direct =>
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      (∃ n < Nat.card Direct, ∃ continuation : Direct,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
            Sum.inl continuation ∧
          rank continuation < rank (advance^[n] start)) ∨
      (Nonempty (Fin 2 ↪ Direct) ∧ Nonempty (Fin 2 ↪ Token)) ∨
      ∃ startIndex stopIndex first stop : Nat,
        startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧
        (advance^[startIndex] start) = (advance^[stopIndex] start) ∧
        (∀ q, startIndex ≤ q -> q < stopIndex ->
          ∃ continuation : Direct,
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
              Sum.inl continuation ∧
            continuation.1 = next (advance^[q] start).1) ∧
        let base := advance^[startIndex] start
        first < stop ∧ stop ≤ stopIndex - startIndex ∧
        (next^[first] base.1) = (next^[stop] base.1) ∧
        (∀ a b : Nat, a < b -> b < stop ->
          (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧
        (∀ q : Nat, first ≤ q -> q < stop ->
          CanonicalStableRawOwnerAdvancingStep
            ends m j k l zero hloop hjk hkl hk0 p hno
              (next^[q] base.1)) ∧
        Nonempty (Fin (stop - first) ↪ Direct) ∧
        Nonempty (Fin (stop - first) ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases
      exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle
        ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | hdrop | hcycle
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hdrop)
  · obtain ⟨startIndex, stopIndex, hlt, hbound, hrepeat, hsteps⟩ :=
      hcycle
    have hclassified : ∀ q, startIndex ≤ q -> q < stopIndex ->
        ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
            Sum.inl continuation ∧
          (continuation.1 = next (advance^[q] start).1 ∨
            (continuation.1.source ≠ (next (advance^[q] start).1).source ∧
              continuation.1.target =
                (next (advance^[q] start).1).target)) := by
      intro q _hqStart hqStop
      obtain ⟨continuation, hstep, _hrank, hkind⟩ := hsteps q hqStop
      exact ⟨continuation, hstep, hkind⟩
    rcases canonicalStableRawComponentDirectCycle_sibling_or_allNext
        ends m j k l zero hloop hjk hkl hk0 p hno component
          start startIndex stopIndex hclassified with
      hsibling | hallNext
    · obtain ⟨q, hqStart, hqStop, continuation, hstep, hkind⟩ :=
        hsibling
      exact Or.inr (Or.inr (Or.inl ⟨
        canonicalStableRawComponentDirectSibling_twoDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind,
        canonicalStableRawComponentDirectSibling_twoTokenEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind⟩))
    · rcases
        canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
          ends m j k l zero hloop hjk hkl hk0 p hno component
            start startIndex stopIndex hlt hrepeat hallNext with
        hpair | hadvancing
      · exact Or.inr (Or.inr (Or.inl hpair))
      · right
        right
        right
        dsimp only at hadvancing ⊢
        obtain ⟨first, stop, hfirstStop, hstopLength, hstate,
          hdistinct, howners, hdirects, htokens⟩ := hadvancing
        exact ⟨startIndex, stopIndex, first, stop, hlt, hbound,
          hrepeat, hallNext, hfirstStop, hstopLength, hstate,
          hdistinct, howners, hdirects, htokens⟩


theorem exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    let Direct := CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let Token := CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let advance := canonicalStableRawComponentDirectForestAdvance
      ends m j k l zero hloop hjk hkl hk0 p hno component
    (∃ n ≤ Nat.card Direct,
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ =
          Sum.inr terminal) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ Direct) ∧
        Nonempty (Fin size ↪ Token) := by
  classical
  dsimp only
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let advance := canonicalStableRawComponentDirectForestAdvance
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  rcases exists_canonicalStableRawComponentDirect_terminal_or_cycle
      ends m j k l zero hloop hjk hkl hk0 p hno component start with
    hterminal | hcycle
  · exact Or.inl hterminal
  · obtain ⟨startIndex, stopIndex, hlt, _hbound, hrepeat, hsteps⟩ :=
      hcycle
    have hclassified : ∀ q, startIndex ≤ q -> q < stopIndex ->
        ∃ continuation : Direct,
          canonicalStableRawComponentForestStep
              ends m j k l zero hloop hjk hkl hk0 p hno component
                ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ =
            Sum.inl continuation ∧
          (continuation.1 = next (advance^[q] start).1 ∨
            (continuation.1.source ≠ (next (advance^[q] start).1).source ∧
              continuation.1.target =
                (next (advance^[q] start).1).target)) := by
      intro q _hqStart hqStop
      obtain ⟨continuation, hstep, hkind⟩ := hsteps q hqStop
      exact ⟨continuation, hstep, hkind⟩
    rcases canonicalStableRawComponentDirectCycle_sibling_or_allNext
        ends m j k l zero hloop hjk hkl hk0 p hno component
          start startIndex stopIndex hclassified with
      hsibling | hallNext
    · obtain ⟨q, _hqStart, _hqStop, continuation, _hstep, hkind⟩ :=
        hsibling
      exact Or.inr ⟨2, by omega,
        canonicalStableRawComponentDirectSibling_twoDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind,
        canonicalStableRawComponentDirectSibling_twoTokenEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (advance^[q] start) continuation hkind⟩
    · rcases
        canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy
          ends m j k l zero hloop hjk hkl hk0 p hno component
            start startIndex stopIndex hlt hrepeat hallNext with
        hpair | hclosed
      · exact Or.inr ⟨2, by omega, hpair.1, hpair.2⟩
      · dsimp only at hclosed
        obtain ⟨first, stop, hfirstStop, _hstopLength, _hstate,
          _hdistinct, _howners, hdirects, htokens⟩ := hclosed
        exact Or.inr ⟨stop - first, by omega, hdirects, htokens⟩


theorem exists_canonicalStableRawComponentDirect_minRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hdirect : Nonempty (CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawSourceRank ends m j k l zero p start.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p direct.1.source := by
  classical
  let Direct := CanonicalStableRawComponentDirectState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let rank := fun direct : Direct =>
    canonicalStableRawSourceRank ends m j k l zero p direct.1.source
  letI : Fintype Direct := Fintype.ofFinite Direct
  obtain ⟨direct⟩ := hdirect
  have huniv : (Finset.univ : Finset Direct).Nonempty :=
    ⟨direct, Finset.mem_univ direct⟩
  have hranks : (Finset.univ.image rank).Nonempty := huniv.image rank
  let minimum := (Finset.univ.image rank).min' hranks
  have hminimum : minimum ∈ Finset.univ.image rank :=
    Finset.min'_mem _ _
  obtain ⟨start, _, hstart⟩ := Finset.mem_image.mp hminimum
  refine ⟨start, ?_⟩
  intro other
  change rank start ≤ rank other
  rw [hstart]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ other, rfl⟩)


end StatMech.GrahamGHS.FourColor
