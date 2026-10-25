/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part58
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

noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.crossingFamily
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sourceBlock i) :
    FiniteRelationDeficiencyOneFamily
      (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) where
  states := insert source (finiteEmbeddingBlock block.size block.sourceBlock)
  tokens := finiteEmbeddingBlock block.size block.tokenBlock
  deficiency_one := by
    have hsourceNotMem : source ∉
        finiteEmbeddingBlock block.size block.sourceBlock := by
      intro hmem
      obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
      exact hsource i heq.symm
    rw [Finset.card_insert_of_notMem hsourceNotMem]
    simp only [finiteEmbeddingBlock, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]

end StatMech.GrahamGHS.FourColor
