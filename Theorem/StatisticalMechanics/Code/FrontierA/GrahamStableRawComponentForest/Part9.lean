/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part9
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

@[simp] theorem FiniteRelationDeficiencyOneFamily.mem_states_extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) :
    source ∈ (family.extendPair source token hsource htoken).states := by
  change source ∈ insert source family.states
  exact Finset.mem_insert_self source family.states

@[simp] theorem FiniteRelationDeficiencyOneFamily.mem_tokens_extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) :
    token ∈ (family.extendPair source token hsource htoken).tokens := by
  change token ∈ insert token family.tokens
  exact Finset.mem_insert_self token family.tokens


end StatMech.GrahamGHS.FourColor
