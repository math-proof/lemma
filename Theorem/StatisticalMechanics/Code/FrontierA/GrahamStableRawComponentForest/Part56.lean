/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part57
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
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingContinuation
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    ∃ continuation : FiniteRelationCrossingContinuation
        (CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      continuation.size = block.size ∧
      let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move
        continuation.natural continuation.natural_incident
      ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧
        (move^[start] continuation.initialHoleState).hole =
          (move^[stop] continuation.initialHoleState).hole ∧
        ∀ a b : Nat, a < b -> b < stop ->
          (move^[a] continuation.initialHoleState).hole ≠
            (move^[b] continuation.initialHoleState).hole := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      _u, _htarget, _hkind, _hcomponent⟩ := hcross
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
      crossing := by
        rw [← htoken]
        exact hincident }
  refine ⟨continuation, rfl, ?_⟩
  simpa only [continuation] using continuation.exists_minimal_hole_repeat


end StatMech.GrahamGHS.FourColor
