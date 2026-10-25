/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part65
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

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle
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
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasPostSecondBacktrack entrance ∨
      block.HasPostSecondLongCycle entrance := by
  classical
  rcases block.exists_postSecond_terminal_or_backtrack_or_longCycle entrance with
    hterminal | hbacktrack | hcycle
  · obtain ⟨n, _hn, token, hstep, _hfresh⟩ := hterminal
    rcases block.postSecondStep_terminal_growth_or_nonexceptional entrance
        _ token hstep with hgrowth | hterminal
    · exact Or.inl hgrowth
    · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hbacktrack))
  · exact Or.inr (Or.inr (Or.inr hcycle))

theorem CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop
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
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      (∃ entrance, block.HasPostSecondBacktrack entrance) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop with
    hgrowth | hself | hescape | hterminal | hrank
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · rcases hescape.augmentedBlock_or_alternate with haugmented |
        ⟨_source, _index, entrance, _hsource, _hcrossing, _hne, _hnatural⟩
    · exact Or.inr (Or.inr (Or.inl haugmented))
    · rcases block.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle
          entrance with hgrowth | hterminal | hbacktrack | hcycle
      · exact Or.inl hgrowth
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨entrance, hbacktrack⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨entrance, hcycle⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrank)))))


theorem partialForestNonbacktrackingStep_eq_inl_relation
    {A B : Type*} (step : A -> A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next ->
      next ≠ current)
    (state next : PartialForestNonbacktrackingState A)
    (hstep : partialForestNonbacktrackingStep step hloopFree state =
      Sum.inl next) :
    step next.1.1 = Sum.inl next.1.2 := by
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
      exact hcontinued

theorem CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance_invariant
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
    (entrance : Fin block.size) (n : Nat) :
    let state := (block.postSecondContinuationAdvance entrance)^[n]
      (block.postSecondInitialState entrance)
    block.postSecondStep entrance state.1.1 = Sum.inl state.1.2 := by
  classical
  induction n with
  | zero =>
      simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondInitialState,
        CanonicalStableRawComponentBalancedDirectBlock.postSecondStep]
  | succ n ih =>
      let previous := (block.postSecondContinuationAdvance entrance)^[n]
        (block.postSecondInitialState entrance)
      have hiterate :
          (block.postSecondContinuationAdvance entrance)^[Nat.succ n]
              (block.postSecondInitialState entrance) =
            block.postSecondContinuationAdvance entrance previous := by
        exact Function.iterate_succ_apply'
          (block.postSecondContinuationAdvance entrance) n
            (block.postSecondInitialState entrance)
      rw [hiterate]
      cases hcontinued : block.postSecondContinuationStep entrance previous with
      | inl next =>
          have hadvance : block.postSecondContinuationAdvance entrance previous =
              next := by
            unfold CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance
            unfold partialForestAdvance
            rw [hcontinued]
          rw [hadvance]
          exact partialForestNonbacktrackingStep_eq_inl_relation
            (block.postSecondStep entrance)
            (block.postSecondStep_continuation_ne entrance)
            previous next hcontinued
      | inr terminal =>
          have hadvance : block.postSecondContinuationAdvance entrance previous =
              previous := by
            unfold CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance
            unfold partialForestAdvance
            rw [hcontinued]
          rw [hadvance]
          exact ih

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_twoCycle
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
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    ∃ previous current : block.PostSecondState,
      previous ≠ current ∧
      block.postSecondStep entrance previous = Sum.inl current ∧
      block.postSecondStep entrance current = Sum.inl previous := by
  obtain ⟨n, _hn, hreverse⟩ := hback
  let state := (block.postSecondContinuationAdvance entrance)^[n]
    (block.postSecondInitialState entrance)
  exact ⟨state.1.1, state.1.2, state.2,
    block.postSecondContinuationAdvance_invariant entrance n, hreverse⟩

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_directIndexTwoCycle
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
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    ∃ previous current : Fin block.size, previous ≠ current ∧
      block.directSuccessorStep previous = Sum.inl current ∧
      block.directSuccessorStep current = Sum.inl previous := by
  obtain ⟨previous, current, hne, hforward, hreverse⟩ := hback.exists_twoCycle
  obtain ⟨previousIndex, hprevious⟩ : ∃ index, previous = Sum.inr index := by
    cases hprevious : previous with
    | inl outside =>
        have hcurrent : current = Sum.inr entrance := by
          simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hprevious] using hforward.symm
        rw [hprevious, hcurrent] at hreverse
        cases hdirect : block.directSuccessorStep entrance <;>
          simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
            hdirect] at hreverse
    | inr index => exact ⟨index, rfl⟩
  obtain ⟨currentIndex, hcurrent⟩ : ∃ index, current = Sum.inr index := by
    cases hcurrent : current with
    | inl outside =>
        rw [hprevious, hcurrent] at hforward
        cases hdirect : block.directSuccessorStep previousIndex with
        | inl retained =>
            simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect] at hforward
        | inr terminal =>
            simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
              hdirect] at hforward
    | inr index => exact ⟨index, rfl⟩
  rw [hprevious, hcurrent] at hne hforward hreverse
  refine ⟨previousIndex, currentIndex, ?_, ?_, ?_⟩
  · intro heq
    exact hne (congrArg Sum.inr heq)
  · cases hdirect : block.directSuccessorStep previousIndex with
    | inl retained =>
        simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] using hforward
    | inr terminal =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] at hforward
  · cases hdirect : block.directSuccessorStep currentIndex with
    | inl retained =>
        simpa [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] using hreverse
    | inr terminal =>
        simp [CanonicalStableRawComponentBalancedDirectBlock.postSecondStep,
          hdirect] at hreverse

theorem CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.threeTokens_or_directTwoCycle
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {entrance : Fin block.size} (hback : block.HasPostSecondBacktrack entrance) :
    let sources := finiteEmbeddingBlock block.size block.sourceBlock
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous) := by
  classical
  dsimp only
  obtain ⟨previous, current, hne, _hforward, _hreverse⟩ :=
    hback.exists_directIndexTwoCycle
  let sources := finiteEmbeddingBlock block.size block.sourceBlock
  let previousState : ↑sources := ⟨block.sourceBlock previous,
    Finset.mem_map.mpr ⟨previous, Finset.mem_univ _, rfl⟩⟩
  let currentState : ↑sources := ⟨block.sourceBlock current,
    Finset.mem_map.mpr ⟨current, Finset.mem_univ _, rfl⟩⟩
  rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        previousState currentState (block.directs previous) (block.directs current)
        (fun heq => hne (block.directs.injective heq)) rfl rfl with
    hthree | hcycle
  · exact Or.inl hthree
  · exact Or.inr ⟨previous, current, hne, hcycle.1, hcycle.2⟩


theorem CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (finiteEmbeddingBlock block.size block.sourceBlock))) ∨
      (∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop with
    hgrowth | hself | haugmented | ⟨entrance, hbacktrack⟩ |
      hcycle | hterminal | hrank
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · exact Or.inr (Or.inr (Or.inl haugmented))
  · rcases hbacktrack.threeTokens_or_directTwoCycle with hthree | htwoCycle
    · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htwoCycle))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcycle)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrank))))))


theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_finiteCycleDischarge
    {I : Type uI} {W : Type uW} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
          problem.rank < Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
          ∀ source : block.StateComplement,
            ∀ token : CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source.1 token ->
                token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasAugmentedIncidentBlock ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (finiteEmbeddingBlock block.size block.sourceBlock))) ∨
      (∃ previous current : Fin block.size, previous ≠ current ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock previous) = Sum.inl (block.directs current) ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨
      (∃ entrance, block.HasPostSecondLongCycle entrance) ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  obtain ⟨block, hclosed | ⟨hcross, _continuation⟩⟩ :=
    hresidual.smallerRecursion_or_crossingContinuation hdeficit
  · exact ⟨block, Or.inl hclosed⟩
  · exact ⟨block, Or.inr
      hcross.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop⟩


end StatMech.GrahamGHS.FourColor
