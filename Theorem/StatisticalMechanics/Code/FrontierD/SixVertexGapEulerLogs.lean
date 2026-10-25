/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapLambertProduct
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem expEuler_eq_pow (t : ℝ) (n : ℕ) :
    Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)) =
      Real.exp (-2 * Real.pi * t) ^ (n + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem summable_expEuler {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))) := by
  have hq0 : 0 ≤ Real.exp (-2 * Real.pi * t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * Real.pi * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have h := (summable_geometric_of_lt_one hq0 hq1).comp_injective Nat.succ_injective
  exact h.congr (fun n => (expEuler_eq_pow t n).symm)

theorem summable_sixVertexEulerLog {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.log
      (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) := by
  have h := (summable_expEuler ht).neg
  simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable h

theorem summable_sixVertexPlusEulerLog {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.log
      (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))) :=
  Real.summable_log_one_add_of_summable (summable_expEuler ht)

theorem sixVertexPlusEulerLog_eq_sub {t : ℝ} (ht : 0 < t) :
    sixVertexPlusEulerLog t = sixVertexEulerLog (2 * t) - sixVertexEulerLog t := by
  have ht2 : 0 < 2 * t := by positivity
  have hs2 := summable_sixVertexEulerLog ht2
  have hs1 := summable_sixVertexEulerLog ht
  rw [sixVertexPlusEulerLog, sixVertexEulerLog, sixVertexEulerLog, ← hs2.tsum_sub hs1]
  apply tsum_congr
  intro n
  let x := Real.exp (-2 * Real.pi * t * (n + 1 : ℝ))
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := by
    dsimp [x]
    rw [Real.exp_lt_one_iff]
    have hn : 0 < (n + 1 : ℝ) := by positivity
    have hp : 0 < 2 * Real.pi * t * (n + 1 : ℝ) := by positivity
    nlinarith
  have htwo : Real.exp (-2 * Real.pi * (2 * t) * (n + 1 : ℝ)) = x ^ 2 := by
    dsimp [x]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [htwo]
  have hm : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.ne'
  have hp : 1 + x ≠ 0 := by positivity
  rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring,
    Real.log_mul hm hp]
  ring


end
end StatMech.FrontierD
