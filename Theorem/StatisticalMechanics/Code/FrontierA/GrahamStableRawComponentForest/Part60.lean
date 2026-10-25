/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part61
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

theorem CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inl
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
    (index next : Fin block.size)
    (hstep : block.directSuccessorStep index = Sum.inl next) :
    next ≠ index ∧
      canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (block.sourceBlock index) = block.tokenBlock next := by
  classical
  unfold CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep at hstep
  dsimp only at hstep
  split at hstep
  next hmem =>
    have hnext : Classical.choose (Finset.mem_map.mp hmem) = next :=
      Sum.inl.inj hstep
    have hchosen := (Classical.choose_spec (Finset.mem_map.mp hmem)).2
    have htoken := hchosen.symm.trans (congrArg block.tokenBlock hnext)
    refine ⟨?_, htoken⟩
    intro hnextIndex
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (block.sourceBlock index)
    exact htoken.trans (congrArg block.tokenBlock hnextIndex)
  next hnot => contradiction

theorem CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inr
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
    (index : Fin block.size)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : block.directSuccessorStep index = Sum.inr token) :
    token = canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (block.sourceBlock index) ∧
      token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  classical
  unfold CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep at hstep
  dsimp only at hstep
  split at hstep
  next hmem => contradiction
  next hnot => exact ⟨Sum.inr.inj hstep.symm, by simpa only [Sum.inr.inj hstep.symm] using hnot⟩

end StatMech.GrahamGHS.FourColor
