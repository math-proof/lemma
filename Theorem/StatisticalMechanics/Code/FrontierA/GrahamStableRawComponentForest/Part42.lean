/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part42
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

theorem canonicalStableRawComponent_tightProperHall
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
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∀ family : Finset ↑sources, family ⊂ Finset.univ ->
      family.card ≤
        (canonicalStableRawComponentRestrictedIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources family).card := by
  classical
  let TightState := ↑sources
  let total := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑total
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  intro family hfamily
  let inclusion : TightState ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let raw := family.map inclusion
  have hrawSubset : raw ⊆ sources := by
    intro state hstate
    obtain ⟨tightState, _htightState, rfl⟩ := Finset.mem_map.mp hstate
    exact tightState.2
  have hrawProper : raw ⊂ sources := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hrawSubset, ?_⟩
    intro heq
    have hlt := Finset.card_lt_card hfamily
    have hrawCard : raw.card = family.card := Finset.card_map _
    have hunivCard : (Finset.univ : Finset TightState).card = sources.card := by
      simp only [Finset.card_univ, TightState, Fintype.card_coe]
    rw [← hrawCard, hunivCard, heq] at hlt
    exact Nat.lt_irrefl _ hlt
  let rawNeighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component raw
  let tightNeighborhood : Finset TightToken :=
    canonicalStableRawComponentRestrictedIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources family
  have hrawNeighborhoodSubset : rawNeighborhood ⊆ total :=
    canonicalStableRawComponentIncidentNeighborhood_mono
      ends m j k l zero hloop hjk hkl hk0 p hno component hrawSubset
  let forward : ↑rawNeighborhood -> ↑tightNeighborhood := fun token =>
    ⟨⟨token.1, hrawNeighborhoodSubset token.2⟩, by
      have hmem := (Finset.mem_filter.mp token.2).2
      obtain ⟨source, hsource, hincident⟩ := hmem
      obtain ⟨state, hstate, hsourceEq⟩ := Finset.mem_map.mp hsource
      subst source
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state, hstate, hincident⟩⟩
  let backward : ↑tightNeighborhood -> ↑rawNeighborhood := fun token =>
    ⟨token.1.1, by
      have hmem := (Finset.mem_filter.mp token.2).2
      obtain ⟨state, hstate, hincident⟩ := hmem
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, state.1,
        Finset.mem_map.mpr ⟨state, hstate, rfl⟩, hincident⟩⟩
  let neighborhoodEquiv : ↑rawNeighborhood ≃ ↑tightNeighborhood :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro token
        apply Subtype.ext
        rfl
      right_inv := by
        intro token
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hneighborhoodCard : rawNeighborhood.card = tightNeighborhood.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr neighborhoodEquiv
  have hhall := hproper raw hrawProper
  have hrawCard : raw.card = family.card := Finset.card_map _
  rw [hrawCard, hneighborhoodCard] at hhall
  simpa only [tightNeighborhood] using hhall


theorem exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
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
      sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources).card + 1 = sources.card ∧
        (∀ source ∈ sources,
          canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (sources.erase source) =
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                sources) ∧
        ∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card := by
  classical
  apply exists_minimal_deficiency_one_family
    (canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (canonicalStableRawComponentIncidentNeighborhood_mono
      ends m j k l zero hloop hjk hkl hk0 p hno component)
  refine ⟨Finset.univ, ?_⟩
  have hneighborhood :
      (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component
          Finset.univ).card ≤
        Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    exact Finset.card_le_univ _
  simpa only [Finset.card_univ] using hneighborhood.trans_lt hdeficit


theorem exists_other_mem_of_incident_of_delete_invariant
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
    (herase : canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (sources.erase source) =
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
    ∃ other ∈ sources, other ≠ source ∧
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component other token := by
  classical
  have htoken : token ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ token,
      source, hsource, hincident⟩
  rw [← herase] at htoken
  obtain ⟨other, hother, hotherIncident⟩ := (Finset.mem_filter.mp htoken).2
  have hotherData := Finset.mem_erase.mp hother
  exact ⟨other, hotherData.2, hotherData.1, hotherIncident⟩


theorem exists_canonicalStableRawComponent_deleteMatching
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
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    ∃ matching : ↑(sources.erase source) ↪
        CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ remaining,
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            remaining.1 (matching remaining) := by
  classical
  let Deleted := ↑(sources.erase source)
  let Token := CanonicalStableRawComponentToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let neighbors : Deleted -> Finset Token := fun remaining =>
    Finset.univ.filter fun token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          remaining.1 token
  have hhall : ∀ family : Finset Deleted,
      family.card ≤ (family.biUnion neighbors).card := by
    intro family
    let inclusion : Deleted ↪
        CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let smaller := family.map inclusion
    have hsmallerSubset : smaller ⊆ sources := by
      intro state hstate
      obtain ⟨remaining, _hremainingFamily, hremaining⟩ :=
        Finset.mem_map.mp hstate
      rw [← hremaining]
      exact Finset.mem_of_mem_erase remaining.2
    have hsourceNot : source ∉ smaller := by
      intro hmem
      obtain ⟨remaining, _hremainingFamily, hremaining⟩ :=
        Finset.mem_map.mp hmem
      apply Finset.ne_of_mem_erase remaining.2
      exact hremaining
    have hsmallerProper : smaller ⊂ sources :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hsmallerSubset, fun heq => hsourceNot (heq ▸ hsource)⟩
    have hcard := hproper smaller hsmallerProper
    have hfamilyCard : smaller.card = family.card := Finset.card_map _
    have hneighborhood :
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component smaller =
          family.biUnion neighbors := by
      ext token
      simp only [canonicalStableRawComponentIncidentNeighborhood,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        smaller, Finset.mem_map]
      constructor
      · rintro ⟨state, ⟨remaining, hremaining, hstate⟩, hincident⟩
        subst state
        refine ⟨remaining, hremaining, ?_⟩
        simpa only [neighbors, Finset.mem_filter, Finset.mem_univ,
          true_and] using hincident
      · rintro ⟨remaining, hremaining, htoken⟩
        refine ⟨remaining.1, ⟨remaining, hremaining, rfl⟩, ?_⟩
        simpa only [neighbors, Finset.mem_filter, Finset.mem_univ,
          true_and] using htoken
    rw [hneighborhood, hfamilyCard] at hcard
    exact hcard
  obtain ⟨matching, hinjective, hincident⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective neighbors).mp hhall
  refine ⟨⟨matching, hinjective⟩, ?_⟩
  intro remaining
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using
    hincident remaining


theorem exists_canonicalStableRawComponent_tightHoleState
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
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 = source ∧
        state.matching.support = Finset.univ.erase state.hole := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨deletedMatching, hdeletedIncident⟩ :=
    exists_canonicalStableRawComponent_deleteMatching
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource hproper
  let liftToken : ↑(sources.erase source) -> TightToken := fun remaining =>
    ⟨deletedMatching remaining, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, remaining.1,
        Finset.mem_of_mem_erase remaining.2, hdeletedIncident remaining⟩⟩
  have hliftInjective : Function.Injective liftToken := by
    intro x y hxy
    apply deletedMatching.injective
    exact congrArg (fun token : TightToken => token.1) hxy
  let hole : TightState := ⟨source, hsource⟩
  let toFun : TightState -> Option TightToken := fun state =>
    if hne : state.1 ≠ source then
      some (liftToken ⟨state.1, Finset.mem_erase.mpr ⟨hne, state.2⟩⟩)
    else none
  have hrelated : ∀ {state token}, toFun state = some token ->
      incident state token := by
    intro state token htoken
    by_cases hne : state.1 ≠ source
    · simp only [toFun, dif_pos hne, Option.some.injEq] at htoken
      subst token
      exact hdeletedIncident
        ⟨state.1, Finset.mem_erase.mpr ⟨hne, state.2⟩⟩
    · simp only [toFun, dif_neg hne] at htoken
      contradiction
  have hinjective : ∀ {x y token}, toFun x = some token ->
      toFun y = some token -> x = y := by
    intro x y token hx hy
    by_cases hxne : x.1 ≠ source
    · by_cases hyne : y.1 ≠ source
      · simp only [toFun, dif_pos hxne, Option.some.injEq] at hx
        simp only [toFun, dif_pos hyne, Option.some.injEq] at hy
        apply Subtype.ext
        have hremaining := hliftInjective (hx.trans hy.symm)
        exact congrArg
          (fun remaining : ↑(sources.erase source) => remaining.1) hremaining
      · simp only [toFun, dif_neg hyne] at hy
        contradiction
    · simp only [toFun, dif_neg hxne] at hx
      contradiction
  let matching : StatMech.FrontierA.RelationPartialMatching incident :=
    ⟨toFun, hrelated, hinjective⟩
  have hsupport : matching.support = Finset.univ.erase hole := by
    ext state
    simp only [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨token, htoken⟩ heq
      subst state
      simp [matching, toFun, hole] at htoken
    · intro hne
      have hrawNe : state.1 ≠ source := by
        intro hraw
        apply hne
        apply Subtype.ext
        exact hraw
      exact ⟨liftToken
          ⟨state.1, Finset.mem_erase.mpr ⟨hrawNe, state.2⟩⟩,
        by simp only [matching, toFun, dif_pos hrawNe]⟩
  have hmaximum : matching.IsMaximum := by
    intro other
    have hother := other.card_support_le_target
    have hmatchingCard : matching.support.card = Fintype.card TightToken := by
      rw [hsupport, Finset.card_erase_of_mem (Finset.mem_univ hole),
        Finset.card_univ]
      change Fintype.card TightState - 1 = Fintype.card TightToken
      simpa only [TightState, TightToken, neighborhood, Fintype.card_coe]
        using congrArg (fun n => n - 1) htight.symm
    rw [hmatchingCard]
    exact hother
  have hholeUnmatched : hole ∉ matching.support := by
    rw [hsupport]
    simp
  exact ⟨⟨matching, hmaximum, hole, hholeUnmatched⟩, rfl, hsupport⟩


theorem exists_canonicalStableRawComponent_saturatedTightHoleState
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
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 = source ∧
        ∀ token : TightToken,
          ∃ matched, state.matching.toFun matched = some token := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨state, hhole, hsupport⟩ :=
    exists_canonicalStableRawComponent_tightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  have hcard : state.matching.support.card = Fintype.card TightToken := by
    rw [hsupport, Finset.card_erase_of_mem (Finset.mem_univ state.hole),
      Finset.card_univ]
    change Fintype.card TightState - 1 = Fintype.card TightToken
    simpa only [TightState, TightToken, neighborhood, Fintype.card_coe]
      using congrArg (fun n => n - 1) htight.symm
  exact ⟨state, hhole, fun token =>
    state.matching.saturates_all_targets_of_card_support_eq hcard token⟩


theorem
    exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens
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
              smaller).card)
    (hthree : Nonempty (Fin 3 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))) :
    Nonempty (Fin 4 ↪ ↑sources) := by
  classical
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  obtain ⟨state, _hhole, hsaturated⟩ :=
    exists_canonicalStableRawComponent_saturatedTightHoleState
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper
  obtain ⟨tokens⟩ := hthree
  simpa only [Nat.reduceAdd] using
    (saturatedHoleState_sourceEmbedding_add_hole state hsaturated 3 tokens)


end StatMech.GrahamGHS.FourColor
