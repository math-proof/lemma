/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part15
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

theorem canonicalStableRawComponentAlternateToken_incident
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
        (canonicalStableRawComponentAlternateToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
  classical
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ s.1).2
  unfold canonicalStableRawComponentAlternateToken
  split
  next hself =>
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p s.1 hself
  next hdirect =>
    exact canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno s.1 hdirect


theorem canonicalStableRawComponentAlternateToken_ne_natural
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
    canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s ≠
      canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  intro heq
  have hraw :
      (canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 =
      (canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s).1 :=
    congrArg (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1) heq
  unfold canonicalStableRawComponentAlternateToken at hraw
  split at hraw
  next hself =>
    change canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s.1 hself =
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


end StatMech.GrahamGHS.FourColor
