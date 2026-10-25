/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogUnregularization
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem abs_log_sub_log_le_of_pos_lower
    {lower x y : Real} (hlower : 0 < lower)
    (hlowerX : lower <= x) (hlowerY : lower <= y) :
    |Real.log x - Real.log y| <= |x - y| / lower := by
  have hx : 0 < x := hlower.trans_le hlowerX
  have hy : 0 < y := hlower.trans_le hlowerY
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x <= Real.log y :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx)
        (Set.mem_Ioi.mpr hy) hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hbasic := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hbasic
    have hdiv : (y - x) / x <= (y - x) / lower :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hlower hlowerX
    have hfinal : Real.log y - Real.log x <= (y - x) / lower := calc
      Real.log y - Real.log x <= y / x - 1 := hbasic
      _ = (y - x) / x := by field_simp [hx.ne']
      _ <= (y - x) / lower := hdiv
    simpa only [neg_sub] using hfinal
  · have hlog : Real.log y <= Real.log x :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hy)
        (Set.mem_Ioi.mpr hx) hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hlog), abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hbasic := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hbasic
    have hdiv : (x - y) / y <= (x - y) / lower :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hlower hlowerY
    calc
      Real.log x - Real.log y <= x / y - 1 := hbasic
      _ = (x - y) / y := by field_simp [hy.ne']
      _ <= (x - y) / lower := hdiv

end
end StatMech.FrontierD
