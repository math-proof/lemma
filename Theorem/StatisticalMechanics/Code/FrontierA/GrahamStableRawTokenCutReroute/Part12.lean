/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part11
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawDirectLeftToken_collisionClosedComponent
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
    canonicalStableRawCollisionClosedLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawDirectLeftToken
            ends m j k l zero hloop hjk hkl hk0 p s hdirect) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawDirectLeftToken
    ends m j k l zero hloop hjk hkl hk0 p s hdirect
  have hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token := by
    unfold token CanonicalStableRawLeftTokenIsExceptional
    unfold canonicalStableRawDirectLeftToken
    simpa only [canonicalStableRawLeftTokenTarget] using s.exceptional
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have ht : t = s := by
    apply canonicalStableRawExceptionalEdge_eq_of_source_target_eq
    · rfl
    · apply Subtype.ext
      rfl
  rw [show canonicalStableRawCollisionClosedLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawCollisionClosedLeftTokenComponent
      rw [dif_pos hexceptional]]
  exact congrArg (canonicalStableRawTokenComponent
    ends m j k l zero hloop hjk hkl hk0 p hno) ht


theorem canonicalStableRawSelfReroute_collisionClosedComponent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawSelfRerouteLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno s hself)) :
    canonicalStableRawCollisionClosedLeftTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          (canonicalStableRawSelfRerouteLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno s hself) =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  classical
  let token := canonicalStableRawSelfRerouteLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno s hself
  let t := canonicalStableRawExceptionalEdgeOfLeftToken
    ends m j k l zero hloop hjk hkl hk0 p token hexceptional
  have htarget : t.target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
    apply Subtype.ext
    rfl
  rw [show canonicalStableRawCollisionClosedLeftTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno token =
      canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno t by
      unfold canonicalStableRawCollisionClosedLeftTokenComponent
      rw [dif_pos hexceptional]]
  rw [canonicalStableRawTokenComponent_eq_of_target_eq
      ends m j k l zero hloop hjk hkl hk0 p hno t
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s) htarget]
  exact canonicalStableRawTokenComponent_next
    ends m j k l zero hloop hjk hkl hk0 p hno s


end StatMech.GrahamGHS.FourColor
