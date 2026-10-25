/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part4
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

def FiniteRelationCrossingContinuation.stateAt
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> A
  | Sum.inl index => continuation.sources index
  | Sum.inr _ => continuation.extra

def FiniteRelationCrossingContinuation.incident
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> continuation.Token -> Prop :=
  fun state token =>
    related (continuation.stateAt state) (continuation.tokens token)

def FiniteRelationCrossingContinuation.natural
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.State -> continuation.Token
  | Sum.inl index => index
  | Sum.inr _ => continuation.index

end StatMech.GrahamGHS.FourColor
