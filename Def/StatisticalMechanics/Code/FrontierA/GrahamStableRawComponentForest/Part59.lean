/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part57
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

def CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput
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
  ∃ source, ∃ index oldIndex : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokenBlock index ∧
    source.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p source.1.source ∧
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u = (block.directs oldIndex).1 ∧
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock index).1 ∧
      CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1 u


def
    CanonicalStableRawComponentBalancedDirectBlock.HasAdvancingOldOutputRankDrop
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
  ∃ source, ∃ index oldIndex : Fin block.size,
    (∀ i, source ≠ block.sourceBlock i) ∧
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source (block.tokenBlock index) ∧
    canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component source =
      block.tokenBlock index ∧
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u = (block.directs oldIndex).1 ∧
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock index).1 ∧
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
      canonicalStableRawSourceRank ends m j k l zero p u.source <
        canonicalStableRawSourceRank ends m j k l zero p source.1.source


end StatMech.GrahamGHS.FourColor
