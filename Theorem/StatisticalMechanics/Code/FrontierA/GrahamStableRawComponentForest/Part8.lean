/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part8
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

theorem FiniteRelationDeficiencyOneFamily.tokenSaturated_or_crossing
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    family.TokenSaturated related ∨
      ∃ source token, related source token ∧ token ∈ family.tokens ∧
        source ∉ family.states := by
  classical
  by_cases hsaturated : family.TokenSaturated related
  · exact Or.inl hsaturated
  · right
    unfold FiniteRelationDeficiencyOneFamily.TokenSaturated at hsaturated
    push Not at hsaturated
    exact hsaturated


theorem FiniteRelationDeficiencyOneFamily.sourceSaturated_or_crossing
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    family.SourceSaturated related ∨
      ∃ source token, related source token ∧ source ∈ family.states ∧
        token ∉ family.tokens := by
  classical
  by_cases hsaturated : family.SourceSaturated related
  · exact Or.inl hsaturated
  · right
    unfold FiniteRelationDeficiencyOneFamily.SourceSaturated at hsaturated
    push Not at hsaturated
    exact hsaturated


end StatMech.GrahamGHS.FourColor
