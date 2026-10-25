/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part49
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

theorem CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_repeat
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
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      orbit.HasStableSuccessorRepeat := by
  rcases orbit.saturationStep_rankSplit with hsaturated | hterminal |
      hextended | ⟨source, u, hsource, hnaturalRepeat,
        htarget, hstable, hcomponent⟩ | hrank
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · rcases orbit.extendBySuccessor_or_repeat source hsource with
      hextended | hrepeat
    · exact Or.inr (Or.inr (Or.inl hextended))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨source, u, hsource, hnaturalRepeat,
          htarget, hstable, hcomponent, hrepeat⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))


theorem CanonicalStableRawTightChargeOrbit.HasStableSuccessorRepeat.originSplit
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
    (hobstruction : orbit.HasStableSuccessorRepeat) :
    (∃ source : ↑sources, ∃ q : Fin orbit.size,
        (∀ i, source ≠ orbit.states i) ∧
        canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          canonicalStableRawComponentTightNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources
              (orbit.states q.succ)) ∨
      (∃ source : ↑sources, ∃ q : Fin orbit.size,
        source.1 ≠ (orbit.states q.succ).1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component source.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q.succ).1) ∨
      ∃ source : ↑sources,
        (∀ i, source ≠ orbit.states i) ∧
        canonicalStableRawComponentTightSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component sources source =
          orbit.tokens orbit.coreFirst := by
  obtain ⟨source, _u, hsource, _hnaturalRepeat, _htarget, _hstable,
      _hcomponent, q, hsuccessorRepeat⟩ := hobstruction
  rcases orbit.origin q with hnatural | hsuccessor | hcore
  · exact Or.inl ⟨source, q, hsource, hsuccessorRepeat.trans hnatural⟩
  · right
    left
    refine ⟨source, q, ?_, ?_⟩
    · intro heq
      exact hsource q.succ (Subtype.ext heq)
    · apply canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
      exact hsuccessorRepeat.trans hsuccessor
  · exact Or.inr (Or.inr
      ⟨source, hsource, hsuccessorRepeat.trans (congrArg orbit.tokens hcore)⟩)


theorem CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_merger
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
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
          canonicalStableRawTokenComponent
                ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
            canonicalStableRawSourceRank ends m j k l zero p u.source <
              canonicalStableRawSourceRank ends m j k l zero p
                source.1.1.source) ∨
      ∃ x y : ↑sources,
        x.1 ≠ y.1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  rcases orbit.saturationStep_grow_or_rankDrop_or_repeat with
    hsaturated | hterminal | hextended | hrank | _hrepeat
  · exact Or.inl hsaturated
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hextended))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrank)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (exists_canonicalStableRawTightComponentForestStepMerger
        ends m j k l zero hloop hjk hkl hk0 p hno component sources htight))))


end StatMech.GrahamGHS.FourColor
