/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part8
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

noncomputable def canonicalStableRawComponentPreferredDirectNext
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hnextPreferred :
      let next := canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
      next.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p
          ⟨canonicalStableRawPreferredRightBase ends m j k l zero
              hloop hjk hkl hk0 p next.target,
            canonicalStableRawPreferredRightBase_mem ends m j k l zero
              hloop hjk hkl hk0 p next.target⟩) :
    CanonicalStableRawComponentPreferredDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
  have hadvance : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 := by
    rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 with
      hadvance | hstable
    · exact hadvance
    · exfalso
      exact (canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 direct.2
          hstable) hnextPreferred
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p direct.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p direct.1.1.target⟩
  have hsource : next.source = owner := Subtype.ext hadvance
  have hdirect : next.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p next.source := by
    intro hself
    apply canonicalStableRawExceptionalEdgeNext_target_ne
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
    calc
      next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p next.source := hself
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := by rw [hsource]
      _ = direct.1.1.target.1 := direct.2.symm
  let nextDirect : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨next, (canonicalStableRawTokenComponent_next
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1).trans
        direct.1.2.1, hdirect⟩
  exact ⟨nextDirect, hnextPreferred⟩


noncomputable def canonicalStableRawComponentPreferredDirectStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentPreferredDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentPreferredDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  intro direct
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
  by_cases hnextPreferred : next.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p next.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p next.target⟩
  · exact Sum.inl
      (canonicalStableRawComponentPreferredDirectNext
        ends m j k l zero hloop hjk hkl hk0 p hno component direct
          hnextPreferred)
  · let raw := canonicalStableRawPreferredFreeLeftToken
        ends m j k l zero hloop hjk hkl hk0 p next.target hnextPreferred
    have hrawComponent : canonicalStableRawFullLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno raw = component := by
      calc
        canonicalStableRawFullLeftTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno raw =
          canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno next :=
          canonicalStableRawPreferredFreeLeftToken_fullComponent
            ends m j k l zero hloop hjk hkl hk0 p hno next hnextPreferred
        _ = canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 :=
          canonicalStableRawTokenComponent_next
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1
        _ = component := direct.1.2.1
    exact Sum.inr ⟨⟨raw, hrawComponent⟩,
      canonicalStableRawPreferredFreeLeftToken_not_exceptional
        ends m j k l zero hloop hjk hkl hk0 p next.target hnextPreferred⟩

end StatMech.GrahamGHS.FourColor
