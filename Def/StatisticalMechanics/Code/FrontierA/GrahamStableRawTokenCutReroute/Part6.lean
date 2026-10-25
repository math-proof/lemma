/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawExceptionalEdgeOfLeftToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token) :
    CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p := by
  classical
  exact {
    source := token.1
    target := canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token
    related := (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase token.2.2)).2
    exceptional := hexceptional }


noncomputable def canonicalStableRawLeftTokenComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token
  · exact StatMech.FrontierA.functionWeakComponent
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno)
      (canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p token hexceptional)
  · exact ∅


end StatMech.GrahamGHS.FourColor
