/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part16
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

theorem canonicalStableRawComponentSuccessorToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component s
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  classical
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ s.1).2
  unfold canonicalStableRawComponentSuccessorToken
  split
  next hself =>
    exact canonicalStableRawSelfOwnerReroute_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself
  next hdirect =>
    exact canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect


theorem canonicalStableRawComponentSuccessorToken_ne_natural
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s ≠
      canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  intro heq
  have hraw :
      (canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      (canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 :=
    congrArg (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1) heq
  unfold canonicalStableRawComponentSuccessorToken at hraw
  split at hraw
  next hself =>
    change canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    unfold canonicalStableRawStateLeftToken at hraw
    rw [dif_pos hself] at hraw
    apply s.1.exceptional
    exact (congrArg (fun token => token.1.1) hraw).symm
  next hdirect =>
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 at hraw
    apply canonicalStableRawDirectAlternateLeftToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect
    exact hraw


theorem canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1 := by
  classical
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos self.2.2]
  exact canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
    ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2 hstable


theorem canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩).1 := by
  classical
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos self.2.2]
  intro heq
  apply next.exceptional
  calc
    next.source.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p self.1.target := hadvancing
    _ = (canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 self.2.2).1.1 := rfl
    _ = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p
              (canonicalStableRawSelfOwnerRerouteLeftToken
                ends m j k l zero hloop hjk hkl hk0 p hno
                  self.1 self.2.2)) := heq
    _ = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p next.target := rfl


end StatMech.GrahamGHS.FourColor
