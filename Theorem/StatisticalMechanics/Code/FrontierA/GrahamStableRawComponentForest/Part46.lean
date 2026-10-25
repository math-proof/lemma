/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part46
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

theorem canonicalStableRawComponentTightSuccessorOther_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    canonicalStableRawComponentTightSuccessorOther
        ends m j k l zero hloop hjk hkl hk0 p hno component
          sources herase state ≠ state := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have hother := exists_other_mem_of_incident_of_delete_invariant
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources state.1 state.2 (herase state.1 state.2) token
      (canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  intro heq
  exact (Classical.choose_spec hother).2.1
    (congrArg Subtype.val heq)

theorem canonicalStableRawComponentTightSuccessorOther_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources state).1 := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have hother := exists_other_mem_of_incident_of_delete_invariant
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources state.1 state.2 (herase state.1 state.2) token
      (canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  exact (Classical.choose_spec hother).2.2


theorem canonicalStableRawComponentTightSuccessorOther_forestStep_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    (∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
          Sum.inl direct ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct)) ∨
      ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
          Sum.inr terminal ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1 terminal.1 := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  have hnext := canonicalStableRawComponentTightSuccessorOther_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 with
  | inl direct =>
      refine Or.inl ⟨direct, rfl, ?_⟩
      exact
        canonicalStableRawComponentTightSuccessorEdge_direct_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            state (next state) hnext direct hstep
  | inr terminal =>
      refine Or.inr ⟨terminal, rfl, ?_⟩
      exact
        canonicalStableRawComponentTightSuccessorEdge_terminal_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            state (next state) hnext terminal hstep


theorem exists_canonicalStableRawComponentTightSuccessorOther_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ start : ↑sources, ∃ a b : Nat,
      a < b ∧ b ≤ Fintype.card ↑sources ∧
        next^[a] start = next^[b] start ∧
        ∀ state, next state ≠ state := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  let start : ↑sources := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  obtain ⟨a, b, hab, hb, hrepeat⟩ :=
    exists_function_iterate_repeat next start
  exact ⟨start, a, b, hab, hb, hrepeat, fun state =>
    canonicalStableRawComponentTightSuccessorOther_ne
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources herase state⟩


theorem
    exists_canonicalStableRawComponentTightSuccessorOther_localized_repeat
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ start : ↑sources, ∃ a b : Nat,
      a < b ∧ b ≤ Fintype.card ↑sources ∧
        next^[a] start = next^[b] start ∧
        (∀ state, next state ≠ state) ∧
        ∀ state,
          (∃ direct : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    state.1 = Sum.inl direct ∧
              CanonicalStableRawComponentIncident
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (next state).1
                  (canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      direct)) ∨
            ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    state.1 = Sum.inr terminal ∧
              CanonicalStableRawComponentIncident
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (next state).1 terminal.1 := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  obtain ⟨start, a, b, hab, hb, hrepeat, hne⟩ :=
    exists_canonicalStableRawComponentTightSuccessorOther_repeat
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hnonempty herase
  exact ⟨start, a, b, hab, hb, hrepeat, hne, fun state =>
    canonicalStableRawComponentTightSuccessorOther_forestStep_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources herase state⟩


theorem exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hnonempty : sources.Nonempty)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ state : ↑sources,
      ¬ canonicalStableRawSourceRank ends m j k l zero p
            (next state).1.1.source <
          canonicalStableRawSourceRank ends m j k l zero p state.1.1.source := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  let rank : ↑sources -> Nat := fun state =>
    canonicalStableRawSourceRank ends m j k l zero p state.1.1.source
  let start : ↑sources := ⟨hnonempty.choose, hnonempty.choose_spec⟩
  by_contra hnone
  have hall (state : ↑sources) : rank (next state) < rank state := by
    by_contra hnot
    exact hnone ⟨state, hnot⟩
  have hbound : ∀ n : Nat,
      rank ((next^[n]) start) + n ≤ rank start := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hdrop := hall ((next^[n]) start)
        omega
  have hfinal := hbound (rank start + 1)
  omega


theorem
    exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ herase : ∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              sources).card + 1 = sources.card ∧
        (∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card) ∧
        let next := canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        ∃ state : ↑sources,
          ¬ canonicalStableRawSourceRank ends m j k l zero p
                (next state).1.1.source <
              canonicalStableRawSourceRank ends m j k l zero p
                state.1.1.source := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, herase, hnonempty, htight, hproper, ?_⟩
  exact exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources hnonempty herase


theorem exists_canonicalStableRawComponent_tightSuccessorOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ next : ↑sources -> ↑sources,
        state.hole.1 = source ∧
        (∀ s, state.matching.toFun (next s) = some (successor s)) ∧
        (∀ s, incident (next s) (successor s)) ∧
        (∀ s, next s ≠ state.hole) ∧
        ∃ i j : Nat, i < j ∧ j ≤ Fintype.card ↑sources ∧
          next^[i] (next state.hole) = next^[j] (next state.hole) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, hhole, hsaturated⟩ :=
    exists_canonicalStableRawComponent_saturatedTightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  let next : TightState -> TightState := fun s =>
    state.matching.targetPreimage hsaturated (successor s)
  have hnext (s : TightState) :
      state.matching.toFun (next s) = some (successor s) :=
    state.matching.targetPreimage_spec hsaturated (successor s)
  have hrelated (s : TightState) : incident (next s) (successor s) :=
    state.matching.related (hnext s)
  have hneHole (s : TightState) : next s ≠ state.hole := by
    intro heq
    apply state.hole_unmatched
    apply (StatMech.FrontierA.RelationPartialMatching.mem_support_iff
      state.matching state.hole).2
    exact ⟨successor s, heq ▸ hnext s⟩
  obtain ⟨i, j, hij, hj, hrepeat⟩ :=
    exists_function_iterate_repeat next (next state.hole)
  exact ⟨state, next, hhole, hnext, hrelated, hneHole,
    i, j, hij, hj, hrepeat⟩


theorem exists_canonicalStableRawComponent_tightSuccessorCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : TightState -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ TightState, ∃ σ : Equiv.Perm (Fin size),
        ∃ tokens : Fin size ↪ TightToken,
          ∃ missing : TightState,
            (∀ i, cycle i ≠ missing) ∧
            (∀ i, tokens i = successor (cycle i)) ∧
            (∀ i, incident (cycle (σ i)) (tokens i)) ∧
            ∃ external : TightState,
              (∀ q, external ≠ cycle q) ∧
              ∃ i, incident external (tokens i) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, next, _hhole, hnext, hrelated, hneHole,
      _a, _b, _hab, _hb, _hrepeat⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  obtain ⟨size, hsize, cycle, σ, hcycle⟩ :=
    exists_function_cycleEmbedding next (next state.hole)
  let tokenMap : Fin size -> TightToken := fun i => successor (cycle i)
  have htokenInjective : Function.Injective tokenMap := by
    intro i q hiq
    have hnextEq : next (cycle i) = next (cycle q) := by
      exact state.matching.injective_some (hnext (cycle i))
        ((hnext (cycle q)).trans (congrArg some hiq.symm))
    have hcycleEq : cycle (σ i) = cycle (σ q) := by
      rw [hcycle i, hcycle q]
      exact hnextEq
    exact σ.injective (cycle.injective hcycleEq)
  let tokens : Fin size ↪ TightToken := ⟨tokenMap, htokenInjective⟩
  have hcycleNeHole (i : Fin size) : cycle i ≠ state.hole := by
    intro heq
    apply hneHole (cycle (σ.symm i))
    calc
      next (cycle (σ.symm i)) = cycle (σ (σ.symm i)) :=
        (hcycle (σ.symm i)).symm
      _ = cycle i := congrArg cycle (σ.apply_symm_apply i)
      _ = state.hole := heq
  letI : DecidableRel incident := fun _ _ => Classical.propDecidable _
  have htightCard : Fintype.card TightToken + 1 =
      Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using htight
  have hproperRelation : ∀ smaller : Finset TightState,
      smaller ⊂ Finset.univ ->
        smaller.card ≤
          (Finset.univ.filter fun token =>
            ∃ source ∈ smaller, incident source token).card := by
    intro smaller hsmaller
    have hhall := canonicalStableRawComponent_tightProperHall
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hproper smaller hsmaller
    simpa only [canonicalStableRawComponentRestrictedIncidentNeighborhood,
      incident] using hhall
  obtain ⟨index, external, hexternal, hexternalIncident⟩ :=
    exists_external_incident_of_tight_properHall
      incident htightCard hproperRelation size hsize cycle tokens
  refine ⟨size, hsize, cycle, σ, tokens, state.hole,
    hcycleNeHole, fun i => rfl, ?_, external, hexternal,
      index, hexternalIncident⟩
  intro i
  change incident (cycle (σ i)) (successor (cycle i))
  rw [hcycle i]
  exact hrelated (cycle i)


theorem canonicalStableRawComponentTightSuccessorEdge_classification
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (s t : ↑sources)
    (hne : s.1 ≠ t.1)
    (ht : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component t.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  have hs := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources s
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1
        s.1 t.1 hs ht
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hne (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans s.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans s.1.2⟩


theorem exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ ↑sources,
        ∃ index : Fin size, ∃ external : ↑sources,
          (∀ q, external ≠ cycle q) ∧
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component external.1
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  sources (cycle index)).1 ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightSuccessorToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources (cycle index)).1 ∧
            (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p
                  (cycle index).1.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p
                  (cycle index).1.1 u) ∧
            canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨size, hsize, cycle, _σ, _tokens, _missing, _hmissing,
      htokens, _hcycleIncident, external, hexternal,
      index, hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  have hexternalSuccessor : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component external.1
        (successor (cycle index)).1 := by
    have heq := htokens index
    exact congrArg Subtype.val heq ▸ hexternalIncident
  have hne : (cycle index).1 ≠ external.1 := by
    intro heq
    apply hexternal index
    exact Subtype.ext heq.symm
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentTightSuccessorEdge_classification
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        (cycle index) external hne hexternalSuccessor
  exact ⟨size, hsize, cycle, index, external, hexternal,
    hexternalSuccessor, u, huTarget, huKind, huComponent⟩


theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_terminal_or_directBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          ∃ tokens : Fin size ↪
              ↑(canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component sources),
            ∀ i,
              canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (directs i) =
                (tokens i).1 := by
  classical
  obtain ⟨size, hsize, _cycle, _σ, tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, _external, _hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  by_cases hallExceptional : ∀ i,
      CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p (tokens i).1.1
  · let exceptionalTokens : Fin size ↪
        CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
      let toExceptional : Fin size ->
          CanonicalStableRawComponentExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
        ⟨(tokens i).1, hallExceptional i⟩
      refine ⟨toExceptional, ?_⟩
      intro i q hiq
      apply tokens.injective
      exact Subtype.ext (congrArg
        (fun token : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component => token.1)
        hiq)
    let exceptionalEquiv :=
      canonicalStableRawComponentDirectStateEquivExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    let directs : Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      exceptionalTokens.trans exceptionalEquiv.symm.toEmbedding
    refine Or.inr ⟨size, hsize, directs, tokens, ?_⟩
    intro i
    change (exceptionalEquiv (exceptionalEquiv.symm (exceptionalTokens i))).1 =
      (tokens i).1
    rw [exceptionalEquiv.apply_symm_apply]
    rfl
  · push_neg at hallExceptional
    obtain ⟨i, hi⟩ := hallExceptional
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨(tokens i).1, hi⟩
    exact Or.inl ⟨terminal, (tokens i).2⟩


theorem
    exists_canonicalStableRawComponent_tightSuccessorBoundary_direct_or_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  obtain ⟨_size, _hsize, cycle, index, _external, _hexternal,
      _hexternalSuccessor, u, huTarget, huKind, huComponent⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  let token := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources (cycle index)
  have hincident := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      sources (cycle index)
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have hmem := canonicalStableRawComponent_directOutput_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        (cycle index) token hincident u huTarget huKind huComponent huDirect
    exact Or.inl ⟨⟨direct, hmem⟩⟩
  · have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact Or.inr ⟨⟨u, huComponent, huSelf⟩⟩


theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ cycle : Fin size ↪ ↑sources,
          ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            ∃ tokens : Fin size ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ external : ↑sources,
                (∀ q, external ≠ cycle q) ∧
                (∀ i,
                  canonicalStableRawComponentDirectEmbedding
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        (directs i) =
                    (tokens i).1) ∧
                (Nonempty (Fin (size + 1) ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  (∃ i, external.1.1 = (directs i).1) ∨
                  ∃ collision : StatMech.FrontierA.crossCollision
                      (canonicalStableRawComponentSelfEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component)
                      (canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component),
                    external.1.1 = collision.1.1.1) := by
  classical
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨size, hsize, cycle, _σ, tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, external, hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  by_cases hallExceptional : ∀ i,
      CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p (tokens i).1.1
  · let exceptionalTokens : Fin size ↪
        CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
      let toExceptional : Fin size ->
          CanonicalStableRawComponentExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component := fun i =>
        ⟨(tokens i).1, hallExceptional i⟩
      refine ⟨toExceptional, ?_⟩
      intro i q hiq
      apply tokens.injective
      exact Subtype.ext (congrArg
        (fun token : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component => token.1)
        hiq)
    let exceptionalEquiv :=
      canonicalStableRawComponentDirectStateEquivExceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    let directs : Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      exceptionalTokens.trans exceptionalEquiv.symm.toEmbedding
    have hdirect (i : Fin size) :
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (directs i) =
          (tokens i).1 := by
      change (exceptionalEquiv
        (exceptionalEquiv.symm (exceptionalTokens i))).1 = (tokens i).1
      rw [exceptionalEquiv.apply_symm_apply]
      rfl
    refine Or.inr ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, ?_⟩
    by_cases hfresh : ∀ i, natural external ≠ tokens i
    · exact Or.inl (finiteEmbedding_add_fresh size tokens
        (natural external) hfresh)
    · push_neg at hfresh
      obtain ⟨i, hi⟩ := hfresh
      have hraw : canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1 := by
        calc
          canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
              (tokens i).1.1 :=
            congrArg (fun token : TightToken => token.1.1) hi
          _ = (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (directs i)).1 := congrArg Subtype.val (hdirect i).symm
          _ = canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1 := rfl
      rcases canonicalStableRawStateLeftToken_eq_imp
          ends m j k l zero hloop hjk hkl hk0 p hno
            external.1.1 (directs i).1 hraw with
        heq | hforward | hreverse
      · exact Or.inr (Or.inl ⟨i, heq⟩)
      · let self : CanonicalStableRawComponentSelfState
            ends m j k l zero hloop hjk hkl hk0 p hno component :=
          ⟨external.1.1, external.1.2, hforward.1⟩
        let collision : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component) :=
          ⟨(self, directs i), by
            apply Subtype.ext
            exact hraw⟩
        exact Or.inr (Or.inr ⟨collision, rfl⟩)
      · exact False.elim ((directs i).2.2 hreverse.1)
  · push_neg at hallExceptional
    obtain ⟨i, hi⟩ := hallExceptional
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨(tokens i).1, hi⟩
    exact Or.inl ⟨terminal, (tokens i).2⟩


theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_fresh_or_exhausts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    ∃ size : Nat, 0 < size ∧
      ∃ cycle : Fin size ↪ TightState,
        ∃ external : TightState,
          (∀ q, external ≠ cycle q) ∧
          (Nonempty (Fin (size + 1) ↪ TightToken) ∨
            ∀ state : TightState,
              state = external ∨ ∃ i, state = cycle i) := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨size, hsize, cycle, _σ, _tokens, _missing, _hmissing,
      _htokens, _hcycleIncident, external, hexternal,
      _index, _hexternalIncident⟩ :=
    exists_canonicalStableRawComponent_tightSuccessorCycle
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  letI : DecidableRel incident := fun _ _ => Classical.propDecidable _
  have hproperRelation : ∀ smaller : Finset TightState,
      smaller ⊂ Finset.univ ->
        smaller.card ≤
          (Finset.univ.filter fun token =>
            ∃ state ∈ smaller, incident state token).card := by
    intro smaller hsmaller
    have hhall := canonicalStableRawComponent_tightProperHall
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources hproper smaller hsmaller
    simpa only [canonicalStableRawComponentRestrictedIncidentNeighborhood,
      incident] using hhall
  have hboundary := tightProperHall_externalSource_freshToken_or_exhausts
    incident hproperRelation size cycle external hexternal
  exact ⟨size, hsize, cycle, external, hexternal, hboundary⟩


theorem canonicalStableRawComponent_no_fullTightTokenBlock_of_exhaustiveCycle
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (size : Nat) (cycle : Fin size ↪ ↑sources) (external : ↑sources)
    (hcover : ∀ state : ↑sources,
      state = external ∨ ∃ i, state = cycle i)
    (htokens : Nonempty (Fin (size + 1) ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))) : False := by
  let cover : Fin size ⊕ Fin 1 -> ↑sources
    | Sum.inl i => cycle i
    | Sum.inr _ => external
  have hsurjective : Function.Surjective cover := by
    intro state
    rcases hcover state with heq | ⟨i, heq⟩
    · exact ⟨Sum.inr 0, by simpa only [cover] using heq.symm⟩
    · exact ⟨Sum.inl i, by simpa only [cover] using heq.symm⟩
  have hsourcesCard : sources.card ≤ size + 1 := by
    have hcard := Fintype.card_le_of_surjective cover hsurjective
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin,
      Nat.add_comm] using hcard
  obtain ⟨tokens⟩ := htokens
  have htokensCard : size + 1 ≤
      (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective tokens tokens.injective
  omega


theorem canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, external.1, external.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ external.1.1).2
  rw [hself]
  exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      collision.1.1.1 collision.1.1.2.2


theorem
    canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, external.1, external.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ external.1.1).2
  rw [hself]
  exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      collision.1.1.1 collision.1.1.2.2


theorem canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
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
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision := by
  intro heq
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component =>
      token.1.1.1) heq
  change collision.1.1.1.source.1 =
    canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p collision.1.1.1.target at hsource
  exact collision.1.1.1.exceptional hsource


theorem
    CanonicalStableRawComponentRichIncidenceBlock.extendByReferenceCharges_or_repeats
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : source.1 = collision.1.1.1) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ q r : Fin (block.size + 1), q ≠ r ∧
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens q ∧
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens r := by
  let sourceToken :=
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  let ownerToken := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hsourceIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source sourceToken := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p sourceToken.1 source.1).2
    rw [hself]
    exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  have hownerIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source ownerToken := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p ownerToken.1 source.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  by_cases hsourceFresh : ∀ q, sourceToken ≠ block.tokens q
  · exact Or.inl
      (block.extend source sourceToken hsource hsourceFresh hsourceIncident)
  · push Not at hsourceFresh
    obtain ⟨q, hq⟩ := hsourceFresh
    by_cases hownerFresh : ∀ r, ownerToken ≠ block.tokens r
    · exact Or.inl
        (block.extend source ownerToken hsource hownerFresh hownerIncident)
    · push Not at hownerFresh
      obtain ⟨r, hr⟩ := hownerFresh
      right
      refine ⟨q, r, ?_, hq, hr⟩
      intro hqr
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact hq.trans (hqr ▸ hr.symm)


theorem
    CanonicalStableRawComponentRichIncidenceBlock.closureStep_localized
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 = canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component source ∧
            ∃ q, canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q) ∨
      (∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          source.1 = direct.1 ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ q r : Fin (block.size + 1), q ≠ r ∧
            canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q ∧
            canonicalStableRawComponentSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens r) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ collision : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          source.1 = collision.1.1.1 ∧
          (∀ i, source ≠ block.sources i) ∧
          ∃ q r s : Fin (block.size + 1), r ≠ s ∧
            canonicalStableRawComponentNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component source =
              block.tokens q ∧
            canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component collision =
              block.tokens r ∧
            canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component collision =
              block.tokens s := by
  rcases block.closureStep_stateClassification with
      hclosed | hextended |
        ⟨source, hsource, ⟨q, hnatural⟩, hterminal | hcollision | hdirect⟩
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hextended)
  · obtain ⟨terminal, hterminal⟩ := hterminal
    exact Or.inr (Or.inr (Or.inl
      ⟨source, hsource, terminal, hterminal, q, hnatural⟩))
  · obtain ⟨collision, hself⟩ := hcollision
    rcases block.extendByReferenceCharges_or_repeats
        source hsource collision hself with hextended | ⟨r, s, hrs, hr, hs⟩
    · exact Or.inr (Or.inl hextended)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, collision, hself, hsource, q, r, s, hrs,
          hnatural, hr, hs⟩)))
  · obtain ⟨direct, hdirect⟩ := hdirect
    rcases block.extendBySuccessor_or_repeat source hsource with
      hextended | ⟨r, hsuccessor⟩
    · exact Or.inr (Or.inl hextended)
    · have hqr : q ≠ r := by
        intro hqr
        apply canonicalStableRawComponentSuccessorToken_ne_natural
          ends m j k l zero hloop hjk hkl hk0 p hno component source
        exact hsuccessor.trans (hqr ▸ hnatural.symm)
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, direct, hdirect, hsource, q, r, hqr,
          hnatural, hsuccessor⟩)))


end StatMech.GrahamGHS.FourColor
