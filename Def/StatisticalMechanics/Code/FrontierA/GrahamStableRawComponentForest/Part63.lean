/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part12
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

noncomputable def partialForestNonbacktrackingStep
    {A B : Type*} (step : A → A ⊕ B)
    (hloopFree : ∀ current next, step current = Sum.inl next →
      next ≠ current) :
    PartialForestNonbacktrackingState A →
      PartialForestNonbacktrackingState A ⊕ (B ⊕ Unit) := by
  classical
  exact fun state =>
    match hstep : step state.1.2 with
    | Sum.inr terminal => Sum.inr (Sum.inl terminal)
    | Sum.inl next =>
        if hback : next = state.1.1 then Sum.inr (Sum.inr ())
        else Sum.inl ⟨(state.1.2, next),
          (hloopFree state.1.2 next hstep).symm⟩

end StatMech.GrahamGHS.FourColor
