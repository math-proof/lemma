/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part58
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

theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_alternate
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
    (hescape : block.HasNaturalTokenEscape) :
    block.HasAugmentedIncidentBlock ∨
      ∃ source, ∃ index q : Fin block.size,
        (∀ i, source ≠ block.sourceBlock i) ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            source (block.tokenBlock index) ∧
        q ≠ index ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokenBlock q := by
  obtain ⟨source, index, hsource, hcrossing, hnatural⟩ := hescape
  rcases hnatural with hfresh | ⟨q, hq, hnatural⟩
  · left
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have htokenFresh : ∀ i, natural ≠ block.tokenBlock i := by
      intro i hi
      apply hfresh
      apply Finset.mem_map.mpr
      exact ⟨i, Finset.mem_univ _, hi.symm⟩
    obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
      finiteEmbedding_snoc block.size block.sourceBlock source hsource
    obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
      finiteEmbedding_snoc block.size block.tokenBlock natural htokenFresh
    refine ⟨extendedSources, extendedTokens, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · rw [hsourceLast, htokenLast]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    · rw [hsourcePrefix, htokenPrefix]
      exact block.sourceBlock_tokenBlock_incident q
  · right
    exact ⟨source, index, q, hsource, hcrossing, hq, hnatural⟩


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_nonreversingContinuation
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
    (hescape : block.HasNaturalTokenEscape) :
    block.HasAugmentedIncidentBlock ∨
      ∃ continuation : FiniteRelationCrossingContinuation
          (CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        continuation.size = block.size ∧
        ∃ alternate : continuation.Token,
          alternate ≠ continuation.index ∧
          continuation.incident (Sum.inr ()) alternate ∧
          let moved := continuation.initialHoleState.move
            continuation.natural continuation.natural_incident
          ∃ hincident' : continuation.incident moved.hole alternate,
            (moved.moveAcross alternate hincident').hole =
              Sum.inl alternate := by
  rcases hescape.augmentedBlock_or_alternate with haugmented |
      ⟨source, index, q, hsource, hcrossing, hq, hnatural⟩
  · exact Or.inl haugmented
  · right
    let continuation : FiniteRelationCrossingContinuation
        (CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      { size := block.size
        sources := block.sourceBlock
        tokens := block.tokenBlock
        extra := source
        index := index
        extra_fresh := hsource
        aligned := block.sourceBlock_tokenBlock_incident
        crossing := hcrossing }
    have halternate : continuation.incident (Sum.inr ()) q := by
      change CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          source (block.tokenBlock q)
      rw [← hnatural]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    refine ⟨continuation, rfl, q, hq, halternate, ?_⟩
    exact continuation.moveThenAlternate_hole q hq halternate


end StatMech.GrahamGHS.FourColor
