/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part34
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

def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :=
  { sources : Fin block.size ↪ CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component //
    ∀ i, CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (sources i) (block.tokens i.castSucc) }


def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (config : block.PivotConfiguration) :
    CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component where
  size := block.size
  positive := block.positive
  sources := config.1
  tokens := block.tokens
  paired := config.2
  extra_nonexceptional := block.extra_nonexceptional


def CanonicalStableRawComponentRichIncidenceBlock.basePivotConfiguration
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
    block.PivotConfiguration := ⟨block.sources, block.paired⟩


def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (current next : block.PivotConfiguration) : Prop :=
  ∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ hsource : ∀ i, source ≠ current.1 i,
      ∃ index : Fin block.size,
        ∃ hincident : CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component source
            (block.tokens index.castSucc),
          next.1 = finiteEmbedding_replaceAt
            current.1 source hsource index


noncomputable def CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.rankSum
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (config : block.PivotConfiguration) : Nat :=
  ∑ i, canonicalStableRawSourceRank ends m j k l zero p
    (config.1 i).1.source

end StatMech.GrahamGHS.FourColor
