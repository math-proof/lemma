/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapLambertProduct
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexAlternatingPlusEulerLog_eq {t : ℝ} (ht : 0 < t) :
    sixVertexAlternatingPlusEulerLog t =
      sixVertexPlusEulerLog t - 2 * sixVertexPlusEulerLog (2 * t) := by
  let f : ℕ → ℝ := fun n => Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))
  have hf : Summable f := summable_sixVertexPlusEulerLog ht
  have he : Summable (fun k => f (2 * k)) := hf.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have ho : Summable (fun k => f (2 * k + 1)) := hf.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  have hsplit := tsum_even_add_odd he ho
  have hodd : (∑' k : ℕ, f (2 * k + 1)) = sixVertexPlusEulerLog (2 * t) := by
    rw [sixVertexPlusEulerLog]
    apply tsum_congr
    intro k
    dsimp [f]
    congr 2
    congr 1
    push_cast
    ring
  rw [sixVertexAlternatingPlusEulerLog]
  change (∑' n : ℕ, (-1 : ℝ) ^ n * f n) = _
  have halt : (∑' n : ℕ, (-1 : ℝ) ^ n * f n) =
      (∑' k : ℕ, f (2 * k)) - ∑' k : ℕ, f (2 * k + 1) := by
    have hse : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k) * f (2 * k))
        (∑' k : ℕ, f (2 * k)) := by
      simpa using he.hasSum
    have hso : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) * f (2 * k + 1))
        (-∑' k : ℕ, f (2 * k + 1)) := by
      convert ho.hasSum.neg using 1
      ext k
      rw [pow_add, pow_mul]
      norm_num
    have hall : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n)
        ((∑' k : ℕ, f (2 * k)) + (-∑' k : ℕ, f (2 * k + 1))) :=
      HasSum.even_add_odd hse hso
    simpa only [sub_eq_add_neg] using hall.tsum_eq
  rw [halt, hodd]
  change (∑' k : ℕ, f (2 * k)) + (∑' k : ℕ, f (2 * k + 1)) =
    sixVertexPlusEulerLog t at hsplit
  linarith

theorem sixVertexAlternatingPlusEulerLog_eq_euler {t : ℝ} (ht : 0 < t) :
    sixVertexAlternatingPlusEulerLog t =
      3 * sixVertexEulerLog (2 * t) - sixVertexEulerLog t -
        2 * sixVertexEulerLog (4 * t) := by
  rw [sixVertexAlternatingPlusEulerLog_eq ht,
    sixVertexPlusEulerLog_eq_sub ht,
    sixVertexPlusEulerLog_eq_sub (show 0 < 2 * t by positivity)]
  ring_nf

theorem sixVertexGapAlternatingLogSeries_eq_euler
    {lam : ℝ} (hlam : 0 < lam) :
    sixVertexGapAlternatingLogSeries lam =
      3 * sixVertexEulerLog (2 * (lam / Real.pi)) -
        sixVertexEulerLog (lam / Real.pi) -
        2 * sixVertexEulerLog (4 * (lam / Real.pi)) := by
  have ht : 0 < lam / Real.pi := div_pos hlam Real.pi_pos
  rw [← sixVertexAlternatingPlusEulerLog_eq_euler ht]
  rw [sixVertexGapAlternatingLogSeries, sixVertexAlternatingPlusEulerLog]
  apply tsum_congr
  intro n
  congr 3
  congr 1
  field_simp [Real.pi_ne_zero]


end
end StatMech.FrontierD
