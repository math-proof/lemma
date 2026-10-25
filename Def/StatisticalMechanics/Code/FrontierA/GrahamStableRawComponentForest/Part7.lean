/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part6
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

def FiniteRelationBlockClosed
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) : Prop :=
  ∀ source token, related source token ->
    ((∃ i, source = sources i) ↔ ∃ i, token = tokens i)


def FiniteRelationTokenClosed
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) : Prop :=
  ∀ source token, related source token ->
    (∃ i, token = tokens i) -> ∃ i, source = sources i


def finiteRelationComplement
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteEmbeddingComplement size sources ->
      FiniteEmbeddingComplement size tokens -> Prop :=
  fun source token => related source.1 token.1


end StatMech.GrahamGHS.FourColor
