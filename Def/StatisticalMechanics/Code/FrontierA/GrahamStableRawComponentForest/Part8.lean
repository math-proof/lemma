/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part3
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

def FiniteRelationDeficiencyOneFamily.TokenSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop :=
  ∀ source token, related source token -> token ∈ family.tokens ->
    source ∈ family.states


def FiniteRelationDeficiencyOneFamily.SourceSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop :=
  ∀ source token, related source token -> source ∈ family.states ->
    token ∈ family.tokens

def FiniteRelationDeficiencyOneFamily.IsSaturated
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (related : A -> B -> Prop) (family : FiniteRelationDeficiencyOneFamily A B) :
    Prop := family.TokenSaturated related ∧ family.SourceSaturated related


end StatMech.GrahamGHS.FourColor
