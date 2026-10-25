/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapLambertProduct
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddEulerRatioLog_eq_euler {t : ℝ} (ht : 0 < t) :
    sixVertexOddEulerRatioLog t =
      3 * sixVertexEulerLog (2 * t) - 2 * sixVertexEulerLog t -
        sixVertexEulerLog (4 * t) := by
  let fm : ℕ → ℝ := fun n => Real.log
    (1 - Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  let fp : ℕ → ℝ := fun n => Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  have hfm : Summable fm := summable_sixVertexEulerLog ht
  have hfp : Summable fp := summable_sixVertexPlusEulerLog ht
  have hme : Summable (fun n => fm (2 * n)) := hfm.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hmo : Summable (fun n => fm (2 * n + 1)) := hfm.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hpe : Summable (fun n => fp (2 * n)) := hfp.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hpo : Summable (fun n => fp (2 * n + 1)) := hfp.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hmSplit := tsum_even_add_odd hme hmo
  have hpSplit := tsum_even_add_odd hpe hpo
  have hmOdd : (∑' n, fm (2 * n)) =
      sixVertexEulerLog t - sixVertexEulerLog (2 * t) := by
    have heven : (∑' n, fm (2 * n + 1)) = sixVertexEulerLog (2 * t) := by
      rw [sixVertexEulerLog]
      apply tsum_congr
      intro n
      dsimp [fm]
      congr 2
      congr 1
      push_cast
      ring
    rw [heven] at hmSplit
    change _ + sixVertexEulerLog (2 * t) = sixVertexEulerLog t at hmSplit
    exact eq_sub_of_add_eq hmSplit
  have hpOdd : (∑' n, fp (2 * n)) =
      sixVertexPlusEulerLog t - sixVertexPlusEulerLog (2 * t) := by
    have heven : (∑' n, fp (2 * n + 1)) = sixVertexPlusEulerLog (2 * t) := by
      rw [sixVertexPlusEulerLog]
      apply tsum_congr
      intro n
      dsimp [fp]
      congr 2
      congr 1
      push_cast
      ring
    rw [heven] at hpSplit
    change _ + sixVertexPlusEulerLog (2 * t) = sixVertexPlusEulerLog t at hpSplit
    exact eq_sub_of_add_eq hpSplit
  rw [sixVertexOddEulerRatioLog]
  have hratio : ∀ n : ℕ,
      Real.log
        ((1 + Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ))) /
          (1 - Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ)))) =
        fp (2 * n) - fm (2 * n) := by
    intro n
    dsimp [fp, fm]
    push_cast
    have hx : Real.exp (-2 * Real.pi * t * (2 * n + 1 : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have hn : 0 < (2 * n + 1 : ℝ) := by positivity
      have hp : 0 < 2 * Real.pi * t * (2 * n + 1 : ℝ) := by positivity
      nlinarith
    rw [Real.log_div (by positivity) (sub_ne_zero.mpr hx.ne')]
  rw [tsum_congr hratio, hpe.tsum_sub hme, hpOdd, hmOdd,
    sixVertexPlusEulerLog_eq_sub ht,
    sixVertexPlusEulerLog_eq_sub (show 0 < 2 * t by positivity)]
  ring_nf

theorem sixVertexDualGapPowerSeries_exp_eq_oddEuler (t : ℝ) :
    sixVertexDualGapPowerSeries (Real.exp (-2 * Real.pi * t)) =
      4 * sixVertexOddEulerRatioLog t := by
  rw [sixVertexDualGapPowerSeries, sixVertexOddEulerRatioLog, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [sixVertexDualGapPowerTerm]
  congr 3 <;> rw [← Real.exp_nat_mul] <;> congr 1 <;> push_cast <;> ring_nf

end
end StatMech.FrontierD
