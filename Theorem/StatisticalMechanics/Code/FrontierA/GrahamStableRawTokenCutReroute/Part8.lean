/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part6
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawDirectLeftToken_component
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    canonicalStableRawLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
      (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      StatMech.FrontierA.functionWeakComponent
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno) s := by
  classical
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect) := by
    unfold CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  have hstate : canonicalStableRawExceptionalEdgeOfLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect)
          hexceptional = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · change (canonicalStableRawDirectLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hdirect).1 = s.source
      unfold canonicalStableRawDirectLeftToken
      rfl
    · apply Subtype.ext
      change (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawDirectLeftToken
              ends m j k l zero hloop hjk hkl hk0 p s hdirect)).1 =
        s.target.1
      unfold canonicalStableRawLeftTokenTarget
        canonicalStableRawDirectLeftToken
      rfl
  simp only [canonicalStableRawLeftTokenComponent, hexceptional,
    dite_true, hstate]


end StatMech.GrahamGHS.FourColor
