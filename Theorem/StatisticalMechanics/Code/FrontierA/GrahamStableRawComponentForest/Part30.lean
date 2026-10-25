/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part29
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

theorem exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hfree : (canonicalStableRawComponentSecondAlternateTarget
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor),
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p
                (canonicalStableRawComponentSecondAlternateTarget
                  ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        canonicalStableRawComponentSecondAlternateTarget
          ends m j k l zero hloop hjk hkl hk0 p hno component anchor := by
  classical
  let target := canonicalStableRawComponentSecondAlternateTarget
    ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  obtain ⟨u, huTarget, _huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component anchor
  have hfreeU : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p u.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p u.target⟩ := by
    rw [huTarget]
    exact hfree
  let raw := canonicalStableRawPreferredFreeLeftToken
    ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU
  have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component :=
    (canonicalStableRawPreferredFreeLeftToken_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u hfreeU).trans huComponent
  let token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨raw, hrawComponent⟩
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨token, canonicalStableRawPreferredFreeLeftToken_not_exceptional
      ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU⟩
  refine ⟨terminal, ?_⟩
  change canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p raw = target
  exact (canonicalStableRawPreferredFreeLeftToken_target
    ends m j k l zero hloop hjk hkl hk0 p u.target hfreeU).trans huTarget


theorem exists_canonicalStableRawComponentPreferredSelfOwnerStable_freeTerminal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hpreferredSelf : s.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.1.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.1.target⟩)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s.1).target := by
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s.1
  have hfree :=
    canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hpreferredSelf hstable
  let raw := canonicalStableRawPreferredFreeLeftToken
    ends m j k l zero hloop hjk hkl hk0 p next.target hfree
  have hrawComponent : canonicalStableRawFullLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno raw = component := by
    calc
      canonicalStableRawFullLeftTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno raw =
        canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno next :=
        canonicalStableRawPreferredFreeLeftToken_fullComponent
          ends m j k l zero hloop hjk hkl hk0 p hno next hfree
      _ = canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno s.1 :=
        canonicalStableRawTokenComponent_next
          ends m j k l zero hloop hjk hkl hk0 p hno s.1
      _ = component := s.2
  let token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨raw, hrawComponent⟩
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨token, canonicalStableRawPreferredFreeLeftToken_not_exceptional
      ends m j k l zero hloop hjk hkl hk0 p next.target hfree⟩
  refine ⟨terminal, ?_⟩
  exact canonicalStableRawPreferredFreeLeftToken_target
    ends m j k l zero hloop hjk hkl hk0 p next.target hfree


end StatMech.GrahamGHS.FourColor
