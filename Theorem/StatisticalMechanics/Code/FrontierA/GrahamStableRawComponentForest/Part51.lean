/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part50
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

theorem CanonicalStableRawTightChargeOrbit.saturationStep_localDischarge
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
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.TokenSaturated ∨
      (∃ extended : CanonicalStableRawTightChargeOrbit
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
          extended.size = orbit.size + 1) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  rcases orbit.saturationStep_grow_or_rankDrop_or_merger htight with
    hsaturated | hterminal | hextended | hrank | ⟨x, y, hne, hmerge⟩
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
  · exact Or.inr (Or.inl hextended)
  · exact Or.inr (Or.inr (Or.inl hrank))
  · exact Or.inr (Or.inr (Or.inr
      (canonicalStableRawComponentForestStepMerger_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x y (fun hxy => hne (congrArg Subtype.val hxy)) hmerge)))


theorem CanonicalStableRawTightChargeOrbit.sourceSaturationStep
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
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
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
  rcases orbit.sourceSaturated_or_external_or_chord herase with
    hsaturated | ⟨external, _token, _hincident, hfresh, _htokenFresh⟩ |
      ⟨q, r, hqr, token, hq, hr, _htokenFresh⟩
  · rcases hsaturated.surplusNatural_rankSplit orbit with
      hterminal | ⟨_index, u, _hrepeat, _htarget, hstable, hcomponent⟩ |
        ⟨u, hcomponent, hrank⟩
    · exact Or.inl hterminal
    · exact Or.inr (Or.inr (Or.inl
        ⟨orbit.states 0, u, hstable, hcomponent⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨orbit.states 0, u, hcomponent, hrank⟩)))
  · rcases orbit.extendByNatural_or_repeat external hfresh with
      hextended | ⟨index, hrepeat⟩
    · exact Or.inr (Or.inl hextended)
    · rcases orbit.repeatedNaturalDischarge external hfresh index hrepeat with
        ⟨u, _htarget, hstable, hcomponent⟩ |
          ⟨u, _htarget, hadvancing, hcomponent⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨external, u, hstable, hcomponent⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨external, u, hadvancing, hcomponent⟩)))
  · rcases orbit.internalChordClassification q r hqr token hq hr with
      ⟨u, _htarget, hstable, hcomponent⟩ |
        ⟨u, _htarget, hadvancing, hcomponent⟩
    · exact Or.inr (Or.inr (Or.inl
        ⟨orbit.states q, u, hstable, hcomponent⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨orbit.states q, u, hadvancing, hcomponent⟩)))


theorem
    CanonicalStableRawTightChargeOrbit.bidirectionalSaturationStep_localDischarge
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
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
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
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · rcases orbit.sourceSaturationStep herase with
      hterminal | hextended | hstable | hadvancing | hrank
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterminal))))
    · exact Or.inl hextended
    · exact Or.inr (Or.inl hstable)
    · exact Or.inr (Or.inr (Or.inl hadvancing))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inl hextended
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hlocal)))


theorem exists_canonicalStableRawTightComponent_initialChargeFamily
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
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightState := ↑sources
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : TightState -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ family : FiniteRelationDeficiencyOneFamily TightState TightToken,
      ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
        ∃ third : TightState, ∃ first : TightToken,
          family.states =
              {state.hole, (state.move natural hnatural).hole, third} ∧
          family.tokens = {natural state.hole, first} ∧
          incident state.hole (natural state.hole) ∧
          incident (state.move natural hnatural).hole (natural state.hole) ∧
          incident state.hole first ∧ incident third first := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, _collision, third, first, _hself, _hdirect,
      hthirdNeHole, hthirdNeDirect, hholeNeDirect, _hfirst,
      hnaturalNeFirst, hselfNatural, hdirectNatural,
      hselfFirst, hthirdFirst⟩ :=
    exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  let family : FiniteRelationDeficiencyOneFamily TightState TightToken :=
    FiniteRelationDeficiencyOneFamily.threeTwo
      state.hole (state.move natural hnatural).hole third
      hholeNeDirect hthirdNeHole.symm hthirdNeDirect.symm
      (natural state.hole) first hnaturalNeFirst
  exact ⟨family, state, third, first, rfl, rfl,
    hselfNatural, hdirectNatural, hselfFirst, hthirdFirst⟩


theorem exists_canonicalStableRawTightComponent_initialChargeOrbit
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
      sources.card) :
    ∃ orbit : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      orbit.size = 2 := by
  classical
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, collision, third, first, hself, hdirect,
      hthirdNeHole, hthirdNeDirect, hholeNeDirect, _hfirst,
      hnaturalNeFirst, hselfNatural, hdirectNatural,
      hselfFirst, hthirdFirst⟩ :=
    exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  let direct := (state.move natural hnatural).hole
  let stateMap : Fin 3 -> ↑sources := fun i =>
    Fin.cases state.hole (fun q => Fin.cases direct (fun _ => third) q) i
  have hstateInjective : Function.Injective stateMap := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hholeNeDirect hxy)
    · exact False.elim (hthirdNeHole hxy.symm)
    · exact False.elim (hholeNeDirect hxy.symm)
    · rfl
    · exact False.elim (hthirdNeDirect hxy.symm)
    · exact False.elim (hthirdNeHole hxy)
    · exact False.elim (hthirdNeDirect hxy)
    · rfl
  let states : Fin 3 ↪ ↑sources := ⟨stateMap, hstateInjective⟩
  let tokenMap : Fin 2 ->
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    fun i => Fin.cases (natural state.hole) (fun _ => first) i
  have htokenInjective : Function.Injective tokenMap := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hnaturalNeFirst hxy)
    · exact False.elim (hnaturalNeFirst hxy.symm)
    · rfl
  let tokens : Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨tokenMap, htokenInjective⟩
  let coreSelf : Fin 3 := ⟨0, by omega⟩
  let coreDirect : Fin 3 := ⟨1, by omega⟩
  let coreThird : Fin 3 := ⟨2, by omega⟩
  let coreNatural : Fin 2 := ⟨0, by omega⟩
  let coreFirst : Fin 2 := ⟨1, by omega⟩
  have hnaturalEq : natural state.hole = natural direct := by
    apply Subtype.ext
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
    rw [hself, hdirect]
    exact congrArg Subtype.val collision.2
  refine ⟨⟨2, states, tokens, ?_, coreSelf, coreDirect, coreThird,
    coreNatural, coreFirst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i
    fin_cases i
    · simpa [states, stateMap, tokens, tokenMap, direct] using hdirectNatural
    · simpa [states, stateMap, tokens, tokenMap] using hthirdFirst
  · intro i
    fin_cases i
    · exact Or.inl (by
        simpa [states, stateMap, tokens, tokenMap, direct] using hnaturalEq)
    · exact Or.inr (Or.inr (by simp [coreFirst]))
  · simp [coreSelf, coreDirect]
  · simp [coreSelf, coreThird]
  · simp [coreDirect, coreThird]
  · simp [coreNatural, coreFirst]
  · simpa [states, stateMap, tokens, tokenMap, coreSelf, coreNatural] using
      hselfNatural
  · simpa [states, stateMap, tokens, tokenMap, coreDirect, coreNatural,
      direct] using hdirectNatural
  · simpa [states, stateMap, tokens, tokenMap, coreSelf, coreFirst] using
      hselfFirst
  · simpa [states, stateMap, tokens, tokenMap, coreThird, coreFirst] using
      hthirdFirst


end StatMech.GrahamGHS.FourColor
