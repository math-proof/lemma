/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part33
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem canonicalStableRawLeftSurplusToken_eq_of_source_target_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    {x y : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p}
    (hsource : x.1 = y.1) (htarget : x.2.1 = y.2.1) : x = y := by
  classical
  rcases x with ⟨xsource, xtarget, hx⟩
  rcases y with ⟨ysource, ytarget, hy⟩
  simp only at hsource htarget
  subst ysource
  subst ytarget
  rfl


end StatMech.GrahamGHS.FourColor
