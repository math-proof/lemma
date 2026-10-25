/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part51
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

theorem exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
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
      2 ≤ orbit.size ∧
      ∀ other : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        other.size ≤ orbit.size := by
  classical
  obtain ⟨start, hstart⟩ :=
    exists_canonicalStableRawTightComponent_initialChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hbound : ∀ orbit : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      orbit.size ≤ sources.card := by
    intro orbit
    have hcard := Fintype.card_le_of_injective
      orbit.states orbit.states.injective
    simp only [Fintype.card_fin, Fintype.card_coe] at hcard
    omega
  obtain ⟨orbit, hmax⟩ := exists_sizeMaximalBlock sources.card
    (fun orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources => orbit.size)
    hbound start
  refine ⟨orbit, ?_, hmax⟩
  have hstartMax := hmax start
  rw [hstart] at hstartMax
  exact hstartMax


theorem
    CanonicalStableRawTightChargeOrbit.TokenSaturated.exhaustive_of_sizeMaximal
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
    (hsaturated : orbit.TokenSaturated)
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧
      (∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ i, token = orbit.tokens i) ∧
      orbit.SourceSaturated := by
  classical
  have hstates : ∀ source : ↑sources, ∃ i, source = orbit.states i := by
    intro source
    by_contra hmissing
    push Not at hmissing
    rcases orbit.extendByNatural_or_repeat source hmissing with
      ⟨extended, hextended⟩ | ⟨q, hrepeat⟩
    · have hle := hmax extended
      omega
    · let token := canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hincident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source.1 token.1 :=
        canonicalStableRawComponentTightNaturalToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      obtain ⟨i, hi⟩ := hsaturated source token hincident ⟨q, hrepeat⟩
      exact hmissing i hi
  have hstateSurjective : Function.Surjective orbit.states := by
    intro source
    obtain ⟨i, hi⟩ := hstates source
    exact ⟨i, hi.symm⟩
  have hstateCard : orbit.size + 1 = sources.card := by
    have hcard := Fintype.card_congr
      (Equiv.ofBijective orbit.states
        ⟨orbit.states.injective, hstateSurjective⟩)
    simpa only [Fintype.card_fin, Fintype.card_coe] using hcard
  have htokenCard : Fintype.card (Fin orbit.size) =
      Fintype.card ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
    simp only [Fintype.card_fin, Fintype.card_coe]
    omega
  have htokenBijective : Function.Bijective orbit.tokens :=
    (Fintype.bijective_iff_injective_and_card orbit.tokens).2
      ⟨orbit.tokens.injective, htokenCard⟩
  have htokens : ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ i, token = orbit.tokens i := by
    intro token
    obtain ⟨i, hi⟩ := htokenBijective.2 token
    exact ⟨i, hi.symm⟩
  have hsourceSaturated : orbit.SourceSaturated := by
    intro _source token _hincident _hsource
    exact htokens token
  exact ⟨hstates, htokens, hsourceSaturated⟩


theorem
    CanonicalStableRawTightChargeOrbit.maximalSaturationStep_localDischarge
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
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.HasRetainedSharedTokenOutput ∨
      orbit.HasFreshInternalChordOutput ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  have hnoGrowth : ¬ ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
    rintro ⟨extended, hextended⟩
    have := hmax extended
    omega
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · rcases orbit.sourceSaturated_or_external_or_chord herase with
      hsaturated | ⟨external, _fresh, _hincident, hfresh, _hfreshToken⟩ |
        ⟨q, r, hqr, token, hq, hr, hfreshToken⟩
    · rcases hsaturated.surplusNatural_rankSplit orbit with
        hterminal | ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩ |
          ⟨u, hcomponent, hrank⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
      · let source := orbit.states (0 : Fin (orbit.size + 1))
        let token := canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
        have hsourceIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              source.1 token.1 :=
          canonicalStableRawComponentTightNaturalToken_incident
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source
        have hpairedIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q.succ).1 token.1 := by
          have hpaired := orbit.paired q
          rw [← hrepeat] at hpaired
          exact hpaired
        have hsourceNe : source ≠ orbit.states q.succ := by
          intro heq
          have hindex := orbit.states.injective heq
          have hval := congrArg Fin.val hindex
          simp [source] at hval
        exact Or.inl
          ⟨source, q, token, u, hsourceNe, rfl, rfl, hrepeat,
            hsourceIncident, hpairedIncident, htarget, Or.inl hstable,
            hcomponent⟩
      · exact Or.inr (Or.inr (Or.inl
          ⟨orbit.states 0, u, hcomponent, hrank⟩))
    · rcases orbit.extendByNatural_or_repeat external hfresh with
        hextended | ⟨q, hrepeat⟩
      · exact False.elim (hnoGrowth hextended)
      · let token := canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources external
        have hexternalIncident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              external.1 token.1 :=
          canonicalStableRawComponentTightNaturalToken_incident
            ends m j k l zero hloop hjk hkl hk0 p hno component sources external
        obtain ⟨i, hi⟩ := htokenSaturated external token hexternalIncident
          ⟨q, hrepeat⟩
        exact False.elim (hfresh i hi)
    · rcases orbit.internalChordClassification q r hqr token hq hr with
        ⟨u, htarget, hstable, hcomponent⟩ |
          ⟨u, htarget, hadvancing, hcomponent⟩
      · exact Or.inr (Or.inl
          ⟨q, r, token, u, hqr, hfreshToken, hq, hr, htarget,
            Or.inl hstable, hcomponent⟩)
      · exact Or.inr (Or.inl
          ⟨q, r, token, u, hqr, hfreshToken, hq, hr, htarget,
            Or.inr hadvancing, hcomponent⟩)
  · exact False.elim (hnoGrowth hextended)
  · exact Or.inr (Or.inr (Or.inl hrank))
  · exact Or.inr (Or.inr (Or.inr hlocal))


theorem
    CanonicalStableRawTightChargeOrbit.maximalSaturationStep_sharp
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
    (hmax : ∀ other : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      other.size ≤ orbit.size)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    orbit.HasRetainedSharedTokenOutput ∨
      (∃ source : ↑sources,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.LocalMergerDischarge := by
  have hnoGrowth : ¬ ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
    rintro ⟨extended, hextended⟩
    have hle := hmax extended
    omega
  rcases orbit.saturationStep_localDischarge herase htight with
    htokenSaturated | hextended | hrank | hlocal
  · obtain ⟨_hstates, _htokens, hsourceSaturated⟩ :=
      htokenSaturated.exhaustive_of_sizeMaximal orbit hmax htight
    rcases hsourceSaturated.surplusNatural_rankSplit orbit with
      hterminal | ⟨q, u, hrepeat, htarget, hstable, hcomponent⟩ |
        ⟨u, hcomponent, hrank⟩
    · exact Or.inr (Or.inr (Or.inl hterminal))
    · let source := orbit.states (0 : Fin (orbit.size + 1))
      let token := canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hsourceIncident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source.1 token.1 :=
        canonicalStableRawComponentTightNaturalToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source
      have hpairedIncident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (orbit.states q.succ).1 token.1 := by
        have hpaired := orbit.paired q
        rw [← hrepeat] at hpaired
        exact hpaired
      have hsourceNe : source ≠ orbit.states q.succ := by
        intro heq
        have hindex := orbit.states.injective heq
        have hval := congrArg Fin.val hindex
        simp [source] at hval
      exact Or.inl
        ⟨source, q, token, u, hsourceNe, rfl, rfl, hrepeat,
          hsourceIncident, hpairedIncident, htarget, Or.inl hstable,
          hcomponent⟩
    · exact Or.inr (Or.inl ⟨orbit.states 0, u, hcomponent, hrank⟩)
  · exact False.elim (hnoGrowth hextended)
  · exact Or.inr (Or.inl hrank)
  · exact Or.inr (Or.inr hlocal)


theorem canonicalStableRawComponent_squareOutput_tightDirect_or_self
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
    (state : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (hkind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
    (hcomponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u = component) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, hcomponent, huDirect⟩
    have hmem := canonicalStableRawComponent_directOutput_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        state token hincident u htarget hkind hcomponent huDirect
    exact Or.inl ⟨⟨direct, hmem⟩⟩
  · have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact Or.inr ⟨⟨u, hcomponent, huSelf⟩⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.direct_or_self
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  obtain ⟨source, _q, token, u, _hne, _horigin, _hnatural, _hrepeat,
      hsourceIncident, _hpairedIncident, htarget, hkind, hcomponent⟩ := houtput
  exact canonicalStableRawComponent_squareOutput_tightDirect_or_self
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      source token hsourceIncident u htarget hkind hcomponent


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.direct_or_self
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput) :
    Nonempty (CanonicalStableRawComponentTightDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  obtain ⟨q, _r, token, u, _hqr, _hfresh, hq, _hr,
      htarget, hkind, hcomponent⟩ := houtput
  exact canonicalStableRawComponent_squareOutput_tightDirect_or_self
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      (orbit.states q) token hq u htarget hkind hcomponent


theorem canonicalStableRawComponent_directNaturalSquareOutput_eq
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
    (source : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hnatural : token = canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (htarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (hkind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u)
    (hdirect : source.1.1.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.1.source) :
    CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
      u = source.1.1 := by
  rw [hnatural] at htarget
  rcases hkind with hstable | hadvancing
  · exact ⟨hstable,
      canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
        source.1 hdirect u htarget hstable⟩
  · exact False.elim
      (canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
        source.1 hdirect u htarget hadvancing)


theorem canonicalStableRawComponent_directNaturalIncidence_endpointSplit
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
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hnatural : token = canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState)
    (hsecondIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        secondState.1 token.1) :
    first.1.source = second.1.source ∨
      first.1.source =
        ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p second.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩ := by
  have htokenSource : token.1.1.1 = first.1.source := by
    rw [hnatural]
    change (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1).1 =
      first.1.source
    rw [hfirst]
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg first.2.2]
    rfl
  have hraw := (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p token.1.1 secondState.1.1).1
      hsecondIncident
  rcases hraw.1 with hsource | howner
  · left
    calc
      first.1.source = token.1.1.1 := htokenSource.symm
      _ = secondState.1.1.source := hsource
      _ = second.1.source := congrArg
        (fun state : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p => state.source) hsecond
  · right
    calc
      first.1.source = token.1.1.1 := htokenSource.symm
      _ = ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p secondState.1.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p
              secondState.1.1.target⟩ := howner
      _ = ⟨canonicalStableRawPreferredRightBase
            ends m j k l zero hloop hjk hkl hk0 p second.1.target,
          canonicalStableRawPreferredRightBase_mem
            ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩ := by
        rw [hsecond]


theorem canonicalStableRawComponent_directPair_threeTokens_or_firstStep
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
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
        Sum.inl second := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources secondState
  let firstSuccessor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno secondState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hnaturalsNe : firstNatural ≠ secondNatural := by
    intro heq
    apply hne
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  have hsuccessorNeFirst : firstSuccessor ≠ firstNatural := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1
    exact congrArg Subtype.val heq
  by_cases hsuccessorSecond : firstSuccessor = secondNatural
  · right
    have hsuccessorToken :
        canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second :=
      (congrArg Subtype.val hsuccessorSecond).trans hsecondNatural
    have hsuccessorExceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              firstState.1).1 := by
      rw [congrArg Subtype.val hsuccessorToken]
      change CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno second.1)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg second.2.2]
      exact canonicalStableRawDirectLeftToken_isExceptional
        ends m j k l zero hloop hjk hkl hk0 p second.1 second.2.2
    unfold canonicalStableRawComponentForestStep
    rw [dif_pos hsuccessorExceptional]
    congr 1
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact (canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1
        hsuccessorExceptional).trans hsuccessorToken
  · left
    exact finiteEmbedding_three_of_pairwise_ne
      firstNatural secondNatural firstSuccessor hnaturalsNe
        hsuccessorNeFirst.symm (fun heq => hsuccessorSecond heq.symm)


theorem canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
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
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      (canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 =
          Sum.inl second ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component secondState.1 =
          Sum.inl first) := by
  rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
        firstState secondState first second hne hfirst hsecond with
    hthree | hfirstStep
  · exact Or.inl hthree
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          secondState firstState second first hne.symm hsecond hfirst with
      hthree | hsecondStep
    · exact Or.inl hthree
    · exact Or.inr ⟨hfirstStep, hsecondStep⟩


theorem canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural
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
    (firstState secondState : ↑sources)
    (first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hne : first ≠ second)
    (hfirst : firstState.1.1 = first.1)
    (hsecond : secondState.1.1 = second.1)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)) :
    Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources firstState ∨
      token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources secondState := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources secondState
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno firstState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno secondState.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hnaturalsNe : firstNatural ≠ secondNatural := by
    intro heq
    apply hne
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  by_cases hfirstToken : token = firstNatural
  · exact Or.inr (Or.inl hfirstToken)
  · by_cases hsecondToken : token = secondNatural
    · exact Or.inr (Or.inr hsecondToken)
    · exact Or.inl (finiteEmbedding_three_of_pairwise_ne
        firstNatural secondNatural token hnaturalsNe
          (fun heq => hfirstToken heq.symm) (fun heq => hsecondToken heq.symm))


theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directPair
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ u : CanonicalStableRawExceptionalEdge
                  ends m j k l zero hloop hjk hkl hk0 p,
                token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources source ∧
                token = orbit.tokens q ∧
                u.target = canonicalStableRawLeftTokenTarget
                    ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
                CanonicalStableRawOwnerStableOutput
                    ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧
                u = source.1.1 ∧
                (first.1.source = second.1.source ∨
                  first.1.source =
                    ⟨canonicalStableRawPreferredRightBase
                        ends m j k l zero hloop hjk hkl hk0 p second.1.target,
                      canonicalStableRawPreferredRightBase_mem
                        ends m j k l zero hloop hjk hkl hk0 p
                          second.1.target⟩)) := by
  have houtput' := houtput
  obtain ⟨source, q, token, u, hne, _horigin, hnatural, hrepeat,
      _hsourceIncident, hpairedIncident, htarget, hkind, _hcomponent⟩ :=
    houtput
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        source (orbit.states q.succ) hne with
    hterminal | hthree | hsecond |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecond))
  · have hsourceDirect : source.1.1.target.1 ≠
        canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          source.1.1.source := by
      rw [hfirst]
      exact first.2.2
    obtain ⟨hstable, hu⟩ :=
      canonicalStableRawComponent_directNaturalSquareOutput_eq
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source token hnatural u htarget hkind hsourceDirect
    have hendpoint :=
      canonicalStableRawComponent_directNaturalIncidence_endpointSplit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirst hsecond token
            hnatural hpairedIncident
    exact Or.inr
      ⟨houtput', source, q, first, second, hne, hfirstSecond, hfirst, hsecond,
        token, u, hnatural, hrepeat, htarget, hstable, hu, hendpoint⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directPair
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1) := by
  have houtput' := houtput
  obtain ⟨q, r, _token, _u, hqr, _hfresh, _hq, _hr,
      _htarget, _hkind, _hcomponent⟩ := houtput
  have hne : orbit.states q ≠ orbit.states r := by
    intro heq
    exact hqr (orbit.states.injective heq)
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        (orbit.states q) (orbit.states r) hne with
    hterminal | hthree | hsecond |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecond))
  · exact Or.inr
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_firstDirectStep
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
              Sum.inl second) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
        hfirst, hsecond, _hsquare⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirstSecond hfirst hsecond with
      hthree | hstep
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
          hfirst, hsecond, hstep⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_firstDirectStep
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q).1 = Sum.inl second) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_firstStep
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond with
      hthree | hstep
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', q, r, first, second, hqr, hfirstSecond,
          hfirst, hsecond, hstep⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directTwoCycle
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasRetainedSharedTokenOutput ∧
        ∃ source : ↑sources, ∃ q : Fin orbit.size,
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            source ≠ orbit.states q.succ ∧ first ≠ second ∧
            source.1.1 = first.1 ∧
            (orbit.states q.succ).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
              Sum.inl second ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q.succ).1 = Sum.inl first) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
        hfirst, hsecond, _hsquare⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source (orbit.states q.succ) first second hfirstSecond hfirst hsecond with
      hthree | ⟨hfirstStep, hsecondStep⟩
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', source, q, first, second, hsourceNe, hfirstSecond,
          hfirst, hsecond, hfirstStep, hsecondStep⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directTwoCycle
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      (orbit.HasFreshInternalChordOutput ∧
        ∃ q r : Fin (orbit.size + 1),
          ∃ first second : CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            q ≠ r ∧ first ≠ second ∧
            (orbit.states q).1.1 = first.1 ∧
            (orbit.states r).1.1 = second.1 ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states q).1 = Sum.inl second ∧
            canonicalStableRawComponentForestStep
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  (orbit.states r).1 = Sum.inl first) := by
  rcases houtput.local_or_directPair herase with hlocal |
      ⟨houtput', q, r, first, second, hqr, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl hlocal
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond with
      hthree | ⟨hfirstStep, hsecondStep⟩
    · exact Or.inl (Or.inr (Or.inl hthree))
    · exact Or.inr
        ⟨houtput', q, r, first, second, hqr, hfirstSecond,
          hfirst, hsecond, hfirstStep, hsecondStep⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_naturalTwoCycle
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨
      ∃ q r : Fin (orbit.size + 1),
        ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources),
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            ∃ first second : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              q ≠ r ∧ first ≠ second ∧
              (orbit.states q).1.1 = first.1 ∧
              (orbit.states r).1.1 = second.1 ∧
              (∀ s, token ≠ orbit.tokens s) ∧
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states q).1 token.1 ∧
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states r).1 token.1 ∧
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
              (CanonicalStableRawOwnerStableOutput
                    ends m j k l zero hloop hjk hkl hk0 p
                      (orbit.states q).1.1 u ∨
                CanonicalStableRawOwnerAdvancingOutput
                    ends m j k l zero hloop hjk hkl hk0 p
                      (orbit.states q).1.1 u) ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
              (token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources (orbit.states q) ∨
                token = canonicalStableRawComponentTightNaturalToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      sources (orbit.states r)) ∧
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states q).1 = Sum.inl second ∧
              canonicalStableRawComponentForestStep
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    (orbit.states r).1 = Sum.inl first := by
  obtain ⟨q, r, token, u, hqr, hfresh, hq, hr,
      htarget, hkind, hcomponent⟩ := houtput
  have hstatesNe : orbit.states q ≠ orbit.states r := by
    intro heq
    exact hqr (orbit.states.injective heq)
  rcases canonicalStableRawComponent_distinctTightStates_localDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        (orbit.states q) (orbit.states r) hstatesNe with
    hterminal | hthree | hsecondCharge |
      ⟨first, second, hfirstSecond, hfirst, hsecond⟩
  · exact Or.inl (Or.inl hterminal)
  · exact Or.inl (Or.inr (Or.inl hthree))
  · exact Or.inl (Or.inr (Or.inr hsecondCharge))
  · rcases canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (orbit.states q) (orbit.states r) first second hfirstSecond
            hfirst hsecond token with
      hthree | hnatural
    · exact Or.inl (Or.inr (Or.inl hthree))
    · rcases canonicalStableRawComponent_directPair_threeTokens_or_twoCycle
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (orbit.states q) (orbit.states r) first second hfirstSecond
              hfirst hsecond with
        hthree | ⟨hfirstStep, hsecondStep⟩
      · exact Or.inl (Or.inr (Or.inl hthree))
      · exact Or.inr
          ⟨q, r, token, u, first, second, hqr, hfirstSecond,
            hfirst, hsecond, hfresh, hq, hr, htarget, hkind, hcomponent,
            hnatural, hfirstStep, hsecondStep⟩


end StatMech.GrahamGHS.FourColor
