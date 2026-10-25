/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part7
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

theorem finiteRelationComplement_closed
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hclosed : FiniteRelationBlockClosed related size sources tokens)
    (source : FiniteEmbeddingComplement size sources) (token : B)
    (hrelated : related source.1 token) :
    token ∉ finiteEmbeddingBlock size tokens := by
  intro hmem
  obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
  have hsourceMem : ∃ q, source.1 = sources q :=
    (hclosed source.1 token hrelated).2 ⟨i, heq.symm⟩
  obtain ⟨q, hq⟩ := hsourceMem
  apply source.2
  apply Finset.mem_map.mpr
  exact ⟨q, Finset.mem_univ _, hq.symm⟩


theorem finiteRelationBlockClosed_or_crossing
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteRelationBlockClosed related size sources tokens ∨
      ∃ source token, related source token ∧
        (((∃ i, source = sources i) ∧ ∀ i, token ≠ tokens i) ∨
          ((∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i)) := by
  classical
  by_cases hclosed : FiniteRelationBlockClosed related size sources tokens
  · exact Or.inl hclosed
  · right
    unfold FiniteRelationBlockClosed at hclosed
    push Not at hclosed
    obtain ⟨source, token, hrelated, hnot⟩ := hclosed
    refine ⟨source, token, hrelated, ?_⟩
    tauto


theorem finiteRelationTokenClosed_or_crossing
    {A B : Type*} (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B) :
    FiniteRelationTokenClosed related size sources tokens ∨
      ∃ source token, related source token ∧
        (∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i := by
  classical
  by_cases hclosed : FiniteRelationTokenClosed related size sources tokens
  · exact Or.inl hclosed
  · right
    unfold FiniteRelationTokenClosed at hclosed
    push Not at hclosed
    obtain ⟨source, token, hrelated, htoken, hsource⟩ := hclosed
    exact ⟨source, token, hrelated, hsource, htoken⟩


theorem finiteRelationComplement_tokenClosed
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (related : A -> B -> Prop) (size : Nat)
    (sources : Fin size ↪ A) (tokens : Fin size ↪ B)
    (hclosed : FiniteRelationTokenClosed related size sources tokens)
    (source : FiniteEmbeddingComplement size sources) (token : B)
    (hrelated : related source.1 token) :
    token ∉ finiteEmbeddingBlock size tokens := by
  intro hmem
  obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp hmem
  obtain ⟨q, hq⟩ := hclosed source.1 token hrelated ⟨i, heq.symm⟩
  apply source.2
  apply Finset.mem_map.mpr
  exact ⟨q, Finset.mem_univ _, hq.symm⟩


end StatMech.GrahamGHS.FourColor
