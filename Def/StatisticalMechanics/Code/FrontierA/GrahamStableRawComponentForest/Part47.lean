/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part46
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

def CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction
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
  (∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    (∀ i, source ≠ block.sources i) ∧
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      terminal.1 = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component source ∧
        ∃ q, canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q) ∨
  (∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      source.1 = direct.1 ∧
      (∀ i, source ≠ block.sources i) ∧
      ∃ q r : Fin (block.size + 1), q ≠ r ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q ∧
        canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens r) ∨
  ∃ source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component,
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      source.1 = collision.1.1.1 ∧
      (∀ i, source ≠ block.sources i) ∧
      ∃ q r s : Fin (block.size + 1), r ≠ s ∧
        canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source =
          block.tokens q ∧
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens r ∧
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          block.tokens s


end StatMech.GrahamGHS.FourColor
