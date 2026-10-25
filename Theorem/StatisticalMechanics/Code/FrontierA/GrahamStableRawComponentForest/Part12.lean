/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part12
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

theorem FiniteRelationCrossingContinuation.move_initialHole_eq_extra
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    (continuation.initialHoleState.move
      continuation.natural continuation.natural_incident).hole =
        Sum.inr () := by
  apply continuation.initialMatching.injective_some
  · simpa only [FiniteRelationCrossingContinuation.initialHoleState,
      FiniteRelationCrossingContinuation.natural] using
      continuation.initialHoleState.matching_apply_move_hole
        continuation.natural continuation.natural_incident
  · rfl


theorem FiniteRelationCrossingContinuation.moveThenAlternate_hole
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related)
    (alternate : continuation.Token)
    (hne : alternate ≠ continuation.index)
    (hincident : continuation.incident (Sum.inr ()) alternate) :
    let moved := continuation.initialHoleState.move
      continuation.natural continuation.natural_incident
    ∃ hincident' : continuation.incident moved.hole alternate,
      (moved.moveAcross alternate hincident').hole = Sum.inl alternate := by
  dsimp only
  let moved := continuation.initialHoleState.move
    continuation.natural continuation.natural_incident
  have hmovedHole : moved.hole = Sum.inr () :=
    continuation.move_initialHole_eq_extra
  have hincident' : continuation.incident moved.hole alternate := by
    rw [hmovedHole]
    exact hincident
  refine ⟨hincident', ?_⟩
  apply moved.matching.injective_some
  · exact moved.matching_apply_moveAcross_hole alternate hincident'
  · rw [continuation.initialHoleState.move_matching_apply_of_ne
      continuation.natural continuation.natural_incident]
    · simp [FiniteRelationCrossingContinuation.initialHoleState,
        FiniteRelationCrossingContinuation.initialMatching, hne]
    · intro heq
      exact hne (Sum.inl.inj heq)
    · rw [hmovedHole]
      simp


theorem FiniteRelationCrossingContinuation.exists_minimal_hole_repeat
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move
      continuation.natural continuation.natural_incident
    ∃ start stop : Nat, start < stop ∧ stop ≤ continuation.size + 1 ∧
      (move^[start] continuation.initialHoleState).hole =
        (move^[stop] continuation.initialHoleState).hole ∧
      ∀ a b : Nat, a < b -> b < stop ->
        (move^[a] continuation.initialHoleState).hole ≠
          (move^[b] continuation.initialHoleState).hole := by
  simpa only [FiniteRelationCrossingContinuation.State,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] using
    continuation.initialHoleState.exists_minimal_hole_repeat
      continuation.natural continuation.natural_incident


end StatMech.GrahamGHS.FourColor
