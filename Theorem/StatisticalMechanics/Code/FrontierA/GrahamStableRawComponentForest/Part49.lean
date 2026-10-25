/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part48
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

theorem CanonicalStableRawTightChargeOrbit.sourceSaturated_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.SourceSaturated ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 ∧
          (∃ i, source = orbit.states i) ∧
          ∀ i, token ≠ orbit.tokens i := by
  classical
  by_cases hsaturated : orbit.SourceSaturated
  · exact Or.inl hsaturated
  · right
    unfold CanonicalStableRawTightChargeOrbit.SourceSaturated at hsaturated
    push Not at hsaturated
    obtain ⟨source, token, hincident, hsource, htoken⟩ := hsaturated
    exact ⟨source, token, hincident, hsource, htoken⟩


theorem CanonicalStableRawTightChargeOrbit.sourceSaturated_or_external_or_chord
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
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.SourceSaturated ∨
      (∃ external token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              external.1 token.1 ∧
          (∀ i, external ≠ orbit.states i) ∧
          ∀ i, token ≠ orbit.tokens i) ∨
      ∃ q r : Fin (orbit.size + 1), q ≠ r ∧
        ∃ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states q).1 token.1 ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states r).1 token.1 ∧
          ∀ s, token ≠ orbit.tokens s := by
  classical
  rcases orbit.sourceSaturated_or_crossing with hsaturated |
      ⟨source, token, hincident, ⟨q, hsource⟩, htoken⟩
  · exact Or.inl hsaturated
  · obtain ⟨other, hotherMem, hotherNe, hotherIncident⟩ :=
      exists_other_mem_of_incident_of_delete_invariant
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source.1
          source.2 (herase source.1 source.2) token.1 hincident
    let external : ↑sources := ⟨other, hotherMem⟩
    by_cases hother : ∃ r, external = orbit.states r
    · obtain ⟨r, hr⟩ := hother
      right
      right
      refine ⟨q, r, ?_, token, ?_, ?_, htoken⟩
      · intro hqr
        apply hotherNe
        have heq : source = external := hsource.trans (hqr ▸ hr.symm)
        exact congrArg Subtype.val heq.symm
      · rw [← hsource]
        exact hincident
      · rw [← hr]
        exact hotherIncident
    · right
      left
      refine ⟨external, token, hotherIncident, ?_, htoken⟩
      push Not at hother
      exact hother


theorem CanonicalStableRawTightChargeOrbit.internalChordClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (q r : Fin (orbit.size + 1)) (hqr : q ≠ r)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hq : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q).1 token.1)
    (hr : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states r).1 token.1) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        (orbit.states q).1.1 (orbit.states r).1.1 hq hr with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · apply False.elim
    apply hqr
    apply orbit.states.injective
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  · exact Or.inl
      ⟨u, htarget, hstable, hcomponent.trans (orbit.states q).1.2⟩
  · exact Or.inr
      ⟨u, htarget, hadvancing, hcomponent.trans (orbit.states q).1.2⟩


theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall
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
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∀ source : ↑sources, ∃ i, source = orbit.states i := by
  classical
  let stateVal : ↑sources ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let tokenVal :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ↪
        CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let stateBlock : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Finset.univ.map (orbit.states.trans stateVal)
  let tokenBlock : Finset (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    Finset.univ.map (orbit.tokens.trans tokenVal)
  have hstateSubset : stateBlock ⊆ sources := by
    intro state hstate
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hstate
    exact (orbit.states i).2
  by_contra hexhaustive
  push Not at hexhaustive
  obtain ⟨missing, hmissing⟩ := hexhaustive
  have hmissingBlock : missing.1 ∉ stateBlock := by
    intro hmem
    obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
    apply hmissing i
    apply Subtype.ext
    exact heq.symm
  have hstateProper : stateBlock ⊂ sources := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hstateSubset, ?_⟩
    intro heq
    apply hmissingBlock
    rw [heq]
    exact missing.2
  have hneighborhoodSubset :
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component stateBlock ⊆
        tokenBlock := by
    intro token htoken
    obtain ⟨_huniv, state, hstateBlock, hincident⟩ :=
      Finset.mem_filter.mp htoken
    have hstateSources := hstateSubset hstateBlock
    let tightState : ↑sources := ⟨state, hstateSources⟩
    obtain ⟨i, _hi, hstateEq⟩ := Finset.mem_map.mp hstateBlock
    have htightState : tightState = orbit.states i := by
      apply Subtype.ext
      exact hstateEq.symm
    have htokenSources : token ∈
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ token, state, hstateSources, hincident⟩
    let tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
      ⟨token, htokenSources⟩
    obtain ⟨q, htokenEq⟩ :=
      hsaturated tightState tightToken hincident ⟨i, htightState⟩
    apply Finset.mem_map.mpr
    exact ⟨q, Finset.mem_univ q, congrArg Subtype.val htokenEq.symm⟩
  have hhall := hproper stateBlock hstateProper
  have hstateCard : stateBlock.card = orbit.size + 1 := by
    simp [stateBlock]
  have htokenCard : tokenBlock.card = orbit.size := by
    simp [tokenBlock]
  have hneighborhoodCard :
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component stateBlock).card ≤
        tokenBlock.card := Finset.card_le_card hneighborhoodSubset
  omega


theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hstates : ∀ source : ↑sources, ∃ i, source = orbit.states i) :
    ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ i, token = orbit.tokens i := by
  classical
  intro token
  obtain ⟨_huniv, source, hsource, hincident⟩ :=
    Finset.mem_filter.mp token.2
  let tightSource : ↑sources := ⟨source, hsource⟩
  obtain ⟨i, hi⟩ := hstates tightSource
  exact hsaturated tightSource token hincident ⟨i, hi⟩


theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive
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
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧
      ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ i, token = orbit.tokens i := by
  have hstates :=
    CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall
      orbit hsaturated hproper
  exact ⟨hstates,
    CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive
      orbit hsaturated hstates⟩


theorem CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated) :
    ∃ q, canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (orbit.states 0) = orbit.tokens q ∧
      ((∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
  let surplus : Fin (orbit.size + 1) := 0
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states surplus)
  have hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states surplus)
  obtain ⟨q, hrepeat⟩ := hsaturated (orbit.states surplus) natural hnatural
    ⟨surplus, rfl⟩
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 natural.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  have hindexNe : surplus ≠ q.succ := by
    intro heq
    have hval := congrArg Fin.val heq
    simp [surplus] at hval
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno natural.1
        (orbit.states surplus).1.1 (orbit.states q.succ).1.1
          hnatural hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exfalso
    apply hindexNe
    apply orbit.states.injective
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  · exact ⟨q, hrepeat, Or.inl
      ⟨u, htarget, hstable, hcomponent.trans (orbit.states surplus).1.2⟩⟩
  · exact ⟨q, hrepeat, Or.inr
      ⟨u, htarget, hadvancing, hcomponent.trans (orbit.states surplus).1.2⟩⟩


theorem
    CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNatural_rankSplit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (hsaturated : orbit.SourceSaturated) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ q, ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources
                (orbit.states 0) = orbit.tokens q ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    (orbit.states 0)).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p
                (orbit.states 0).1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
        canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              (orbit.states 0).1.1.source := by
  classical
  obtain ⟨q, hrepeat, hstable | hadvancing⟩ :=
    hsaturated.surplusNaturalDischarge orbit
  · obtain ⟨u, htarget, hstable, hcomponent⟩ := hstable
    exact Or.inr (Or.inl
      ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩)
  · obtain ⟨u, htarget, hadvancing, hcomponent⟩ := hadvancing
    rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states 0) with
      hterminal | ⟨collision, hself, _htoken⟩ | ⟨direct, hdirect⟩
    · exact Or.inl hterminal
    · have hsourceSelf : (orbit.states 0).1.1.target.1 =
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.source := by
        rw [hself]
        exact collision.1.1.2.2
      let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
        ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p
              (orbit.states 0).1.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p
              (orbit.states 0).1.1.target⟩
      have hownerRank : canonicalStableRawSourceRank
            ends m j k l zero p owner <
          canonicalStableRawSourceRank ends m j k l zero p
            (orbit.states 0).1.1.source :=
        canonicalStableRawPreferredRightBase_rank_lt_of_self
          ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.target (orbit.states 0).1.1.source
              hsourceSelf.symm (orbit.states 0).1.1.exceptional
      have huSource : u.source = owner := by
        apply Subtype.ext
        exact hadvancing
      exact Or.inr (Or.inr
        ⟨u, hcomponent, huSource ▸ hownerRank⟩)
    · have hsourceDirect : (orbit.states 0).1.1.target.1 ≠
          canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
            (orbit.states 0).1.1.source := by
        rw [hdirect]
        exact direct.2.2
      exact False.elim
        (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
          (orbit.states 0).1 hsourceDirect u htarget hadvancing)


theorem CanonicalStableRawTightChargeOrbit.tokenSaturated_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 ∧
          (∀ i, source ≠ orbit.states i) ∧ ∃ i, token = orbit.tokens i := by
  classical
  by_cases hsaturated : orbit.TokenSaturated
  · exact Or.inl hsaturated
  · right
    unfold CanonicalStableRawTightChargeOrbit.TokenSaturated at hsaturated
    push Not at hsaturated
    obtain ⟨source, token, hincident, hold, hfresh⟩ := hsaturated
    exact ⟨source, token, hincident, hfresh, hold⟩


theorem CanonicalStableRawTightChargeOrbit.extendByNatural_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i) :
    (∃ extended : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        extended.size = orbit.size + 1) ∨
      ∃ i, canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens i := by
  classical
  let charge := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  by_cases hfresh : ∀ i, charge ≠ orbit.tokens i
  · left
    exact orbit.extendPair source charge hsource hfresh
      (canonicalStableRawComponentTightNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
      (Or.inl rfl)
  · right
    push Not at hfresh
    exact hfresh


theorem CanonicalStableRawTightChargeOrbit.extendBySuccessor_or_repeat
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i) :
    (∃ extended : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        extended.size = orbit.size + 1) ∨
      ∃ i, canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
        orbit.tokens i := by
  classical
  let charge := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  by_cases hfresh : ∀ i, charge ≠ orbit.tokens i
  · left
    exact orbit.extendPair source charge hsource hfresh
      (canonicalStableRawComponentTightSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
      (Or.inr rfl)
  · right
    push Not at hfresh
    exact hfresh


theorem CanonicalStableRawTightChargeOrbit.repeatedSuccessorDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i)
    (q : Fin orbit.size)
    (hrepeat : canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
      orbit.tokens q) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightSuccessorToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hnew : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 successor.1 :=
    canonicalStableRawComponentTightSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 successor.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno successor.1
        source.1.1 (orbit.states q.succ).1.1 hnew hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource q.succ (Subtype.ext (Subtype.ext heq)))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.1.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.1.2⟩


theorem CanonicalStableRawTightChargeOrbit.repeatedNaturalDischarge
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources) (hsource : ∀ i, source ≠ orbit.states i)
    (q : Fin orbit.size)
    (hrepeat : canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
      orbit.tokens q) :
    (∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawComponentTightNaturalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component sources
                  source).1.1 ∧
        CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hnew : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 natural.1 :=
    canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source
  have hold : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (orbit.states q.succ).1 natural.1 := by
    have hpaired := orbit.paired q
    rw [← hrepeat] at hpaired
    exact hpaired
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno natural.1
        source.1.1 (orbit.states q.succ).1.1 hnew hold with
    heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource q.succ (Subtype.ext (Subtype.ext heq)))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.1.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.1.2⟩


theorem CanonicalStableRawTightChargeOrbit.saturationStep
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      ∃ source : ↑sources, (∀ i, source ≠ orbit.states i) ∧
        ∃ q, canonicalStableRawComponentTightNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          orbit.tokens q := by
  classical
  rcases orbit.tokenSaturated_or_crossing with hsaturated |
      ⟨source, _oldToken, _hcrossing, hsource, _hold⟩
  · exact Or.inl hsaturated
  · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source with
      hterminal | _hcollision | _hdirect
    · exact Or.inr (Or.inl hterminal)
    · rcases orbit.extendByNatural_or_repeat source hsource with hextend | hrepeat
      · exact Or.inr (Or.inr (Or.inl hextend))
      · exact Or.inr (Or.inr (Or.inr ⟨source, hsource, hrepeat⟩))
    · rcases orbit.extendByNatural_or_repeat source hsource with hextend | hrepeat
      · exact Or.inr (Or.inr (Or.inl hextend))
      · exact Or.inr (Or.inr (Or.inr ⟨source, hsource, hrepeat⟩))


theorem CanonicalStableRawTightChargeOrbit.saturationStep_classified
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  rcases orbit.saturationStep with hsaturated | hterminal | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨u, _htarget, hstable, hcomponent⟩ |
        ⟨u, _htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, hstable, hcomponent⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, hadvancing, hcomponent⟩)))


theorem CanonicalStableRawTightChargeOrbit.saturationStep_rankSplit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.TokenSaturated ∨
      (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          (∀ i, source ≠ orbit.states i) ∧
          (∃ r, canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
            orbit.tokens r) ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentTightNaturalToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources
                    source).1.1 ∧
          CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      ∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source := by
  classical
  rcases orbit.saturationStep with hsaturated | hterminal | hextended |
      ⟨source, hsource, q, hrepeat⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.repeatedNaturalDischarge source hsource q hrepeat with
      ⟨u, htarget, hstable, hcomponent⟩ |
        ⟨u, htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨source, u, hsource, ⟨q, hrepeat⟩,
          htarget, hstable, hcomponent⟩)))
    · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source with
        hterminal | ⟨collision, hself, _htoken⟩ | ⟨direct, hdirect⟩
      · exact Or.inr (Or.inl hterminal)
      · have hsourceSelf : source.1.1.target.1 =
            canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.source := by
          rw [hself]
          exact collision.1.1.2.2
        let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.target,
            canonicalStableRawPreferredRightBase_mem
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.target⟩
        have hownerRank : canonicalStableRawSourceRank
              ends m j k l zero p owner <
            canonicalStableRawSourceRank
              ends m j k l zero p source.1.1.source :=
          canonicalStableRawPreferredRightBase_rank_lt_of_self
            ends m j k l zero hloop hjk hkl hk0 p source.1.1.target
              source.1.1.source hsourceSelf.symm source.1.1.exceptional
        have huSource : u.source = owner := by
          apply Subtype.ext
          exact hadvancing
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨source, u, hcomponent, huSource ▸ hownerRank⟩)))
      · have hsourceDirect : source.1.1.target.1 ≠
            canonicalStableRawSelfBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.1.source := by
          rw [hdirect]
          exact direct.2.2
        exact False.elim
          (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
            source.1 hsourceDirect u htarget hadvancing)


end StatMech.GrahamGHS.FourColor
