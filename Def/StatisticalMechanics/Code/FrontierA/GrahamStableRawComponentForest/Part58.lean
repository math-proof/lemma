/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part56
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

def CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source token, ∃ index oldIndex : Fin block.size,
    CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
      (∀ i, source ≠ block.sourceBlock i) ∧
      token = block.tokenBlock index ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u = (block.directs oldIndex).1 ∧
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p source.1 u)


def CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape
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
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ source, ∃ index : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    let natural := canonicalStableRawComponentNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    natural ∉ finiteEmbeddingBlock block.size block.tokenBlock ∨
      ∃ q, q ≠ index ∧ natural = block.tokenBlock q


def CanonicalStableRawComponentBalancedDirectBlock.HasAugmentedIncidentBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Prop :=
  ∃ sources : Fin (block.size + 1) ↪
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ tokens : Fin (block.size + 1) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∀ i, CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (sources i) (tokens i)


end StatMech.GrahamGHS.FourColor
