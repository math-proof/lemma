/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part5
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

def CanonicalStableRawComponentRichStrictBlock.sourceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  block.directs.trans
    (canonicalStableRawComponentDirectStateEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)

def CanonicalStableRawComponentRichStrictBlock.tokenPrefix
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  Fin.castSuccEmb.trans block.tokens

def CanonicalStableRawComponentRichIncidenceBlock.tokenPrefix
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fin block.size ↪ CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  Fin.castSuccEmb.trans block.tokens

def CanonicalStableRawComponentRichIncidenceBlock.IsClosed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  FiniteRelationTokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sources block.tokenPrefix


def CanonicalStableRawComponentRichStrictBlock.toIncidenceBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichStrictBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component where
  size := block.size
  positive := block.positive
  sources := block.sourceBlock
  tokens := block.tokens
  paired := by
    intro i
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (block.tokens i.castSucc).1 (block.directs i).1).2
    rw [block.aligned i]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs i).1
  extra_nonexceptional := block.extra_nonexceptional


end StatMech.GrahamGHS.FourColor
