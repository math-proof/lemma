/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SingleTopRun
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2.Part2
import Def.StatisticalMechanics.Code.Onsager.InsideClimb


namespace StatMech.Onsager.InsideClimb

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


theorem cc_eq_four_of_selfAvoidanceWall (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
    (hwall : two_nw_corners_not_injective d) :
    cc d = 4 := by
  have hdvd := four_dvd_cc d hreflexfree
  have hge := four_le_cc d hclosed hreflexfree
  have h8 : cc d < 8 := by
    by_contra hc
    rw [not_lt] at hc
    obtain ⟨i, j, hij, hi1, hi2, hj1, hj2⟩ :=
      StatMech.Onsager.NoDoubleWind2.exists_two_top_corners d hreflexfree hc
    exact hwall i j hij hi1 hi2 hj1 hj2 hsimple
  omega

end StatMech.Onsager.InsideClimb
