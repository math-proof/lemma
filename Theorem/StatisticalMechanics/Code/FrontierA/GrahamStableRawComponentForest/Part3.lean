/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part3
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

@[simp] theorem FiniteRelationMinimalTightProblem.rank_eq_carrier_card
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    problem.rank = problem.carrier.card := by
  simp [FiniteRelationMinimalTightProblem.rank]


theorem FiniteRelationMinimalTightProblem.strongInduction
    (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
    (step : ∀ problem,
      (∀ smaller, smaller.rank < problem.rank -> motive smaller) ->
        motive problem)
    (problem : FiniteRelationMinimalTightProblem.{u, v}) :
    motive problem := by
  induction hrank : problem.rank using Nat.strong_induction_on
      generalizing problem with
  | h rank ih =>
      apply step problem
      intro smaller hsmaller
      exact ih smaller.rank (by simpa only [hrank] using hsmaller) smaller rfl


end StatMech.GrahamGHS.FourColor
