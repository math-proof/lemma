/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part3
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

theorem finiteEmbeddingComplement_card
    {A : Type*} [Fintype A] [DecidableEq A]
    (size : Nat) (block : Fin size ↪ A) :
    Fintype.card (FiniteEmbeddingComplement size block) =
      Fintype.card A - size := by
  classical
  let P := fun a : A => a ∈ finiteEmbeddingBlock size block
  have hsplit := Fintype.card_subtype_compl P
  have hblock : Fintype.card {a : A // P a} = size := by
    simpa only [P, Fintype.card_coe, finiteEmbeddingBlock,
      Finset.card_map, Finset.card_univ, Fintype.card_fin]
  simpa only [P, hblock] using hsplit


end StatMech.GrahamGHS.FourColor
