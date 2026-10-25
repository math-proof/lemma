/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part53
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

theorem
    CanonicalStableRawComponentBalancedDirectBlock.sourceBlock_tokenBlock_incident
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index) (block.tokenBlock index) := by
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p
      (block.tokenBlock index).1 (block.sourceBlock index).1).2
  change CanonicalStableRawStateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (block.directs index).1) (block.directs index).1
  exact canonicalStableRawStateLeftToken_stateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1


theorem
    CanonicalStableRawComponentBalancedDirectBlock.successorToken_fresh_or_retainedOther
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (index : Fin block.size) :
    let successor := canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    successor ∉ finiteEmbeddingBlock block.size block.tokenBlock ∨
      ∃ next, next ≠ index ∧ successor = block.tokenBlock next := by
  dsimp only
  let successor := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (block.sourceBlock index)
  by_cases hmem : successor ∈
      finiteEmbeddingBlock block.size block.tokenBlock
  · right
    obtain ⟨next, _hnext, hnext⟩ := Finset.mem_map.mp hmem
    refine ⟨next, ?_, hnext.symm⟩
    intro hnextIndex
    subst next
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    change successor = block.tokenBlock index
    exact hnext.symm
  · exact Or.inl hmem


end StatMech.GrahamGHS.FourColor
