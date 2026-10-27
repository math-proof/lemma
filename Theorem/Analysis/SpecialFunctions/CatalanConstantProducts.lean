/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.CatalanConstantProducts


section

namespace MetaMathlibExt

theorem catBase_odd (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 3) = (4 * (m : ℝ) + 1) / (4 * (m : ℝ) + 3) := by
  have hne : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := by positivity
  field_simp
  ring

theorem catBase_even (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 5) = (4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 5) := by
  have hne : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := by positivity
  field_simp
  ring

theorem catBase_odd3 (m : ℕ) :
    (1 : ℝ) - 2 / (4 * (m : ℝ) + 7) = (4 * (m : ℝ) + 5) / (4 * (m : ℝ) + 7) := by
  have hne : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := by positivity
  field_simp
  ring

theorem catF_succ_odd (m : ℕ) :
    catF (2 * m + 1) = ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1) := by
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  have hcast : (2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 3 := by
    push_cast
    ring
  unfold catF
  rw [hodd.neg_one_pow, mul_neg_one, zpow_neg, zpow_natCast, hcast,
    catBase_odd, div_pow, div_pow, inv_div]

theorem catF_succ_even (m : ℕ) :
    catF (2 * m + 2) = ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 5)) ^ (2 * m + 2) := by
  have heven : Even (2 * m + 2) := ⟨m + 1, by ring⟩
  have hcast : (2 : ℝ) * ((2 * m + 2 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 5 := by
    push_cast
    ring
  unfold catF
  rw [heven.neg_one_pow, mul_one, zpow_natCast, hcast, catBase_even]

theorem catF_succ_odd3 (m : ℕ) :
    catF (2 * m + 3) = ((4 * (m : ℝ) + 7) / (4 * (m : ℝ) + 5)) ^ (2 * m + 3) := by
  have hodd : Odd (2 * m + 3) := ⟨m + 1, by ring⟩
  have hcast : (2 : ℝ) * ((2 * m + 3 : ℕ) : ℝ) + 1 = 4 * (m : ℝ) + 7 := by
    push_cast
    ring
  unfold catF
  rw [hodd.neg_one_pow, mul_neg_one, zpow_neg, zpow_natCast, hcast,
    catBase_odd3, div_pow, div_pow, inv_div]

/-- The second product is the first times the boundary factor. -/
theorem catQ_eq (m : ℕ) :
    catQ m = catP m * (((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1)) := by
  have h := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m) (f := catF) (by omega)
  rw [show (2 * m) + 1 = 2 * m + 1 from rfl] at h
  unfold catQ catP
  rw [h, catF_succ_odd]

theorem cat_g0 : Filter.Tendsto (fun m : ℕ => (2 : ℝ) / ((4 : ℝ) * m + 1))
    Filter.atTop (nhds 0) := by
  have hup : Filter.Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.mul (tendsto_const_nhds (x := (2 : ℝ)))
      tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun m => by positivity) ?_ hup
  filter_upwards with m
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h3 : (m : ℝ) + 1 ≤ 4 * (m : ℝ) + 1 := by
    have hnn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    linarith
  have h4 : (1 : ℝ) / (4 * (m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
    one_div_le_one_div_of_le h1 h3
  have e1 : (2 : ℝ) / (4 * (m : ℝ) + 1) = 2 * (1 / (4 * (m : ℝ) + 1)) := by
    rw [mul_one_div]
  rw [e1]
  exact mul_le_mul_of_nonneg_left h4 (by norm_num)

theorem cat_mg_half : Filter.Tendsto (fun m : ℕ => (m : ℝ) * (2 / ((4 : ℝ) * m + 1)))
    Filter.atTop (nhds (1 / 2)) := by
  have heq : (fun m : ℕ => (m : ℝ) * (2 / ((4 : ℝ) * m + 1))) =ᶠ[Filter.atTop]
      (fun m : ℕ => (2 : ℝ) / (4 + 1 / (m : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hmc : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h41 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := by positivity
    have h43 : (4 : ℝ) + 1 / (m : ℝ) ≠ 0 := by positivity
    field_simp
  refine Filter.Tendsto.congr' heq.symm ?_
  have hden : Filter.Tendsto (fun m : ℕ => (4 : ℝ) + 1 / (m : ℝ))
      Filter.atTop (nhds 4) := by
    have h := (tendsto_const_nhds (x := (4 : ℝ))).add
      tendsto_one_div_atTop_nhds_zero_nat
    simpa using h
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div hden (by norm_num)
  rwa [show (2 : ℝ) / 4 = 1 / 2 from by norm_num] at h

theorem cat_pow_half : Filter.Tendsto
    (fun m : ℕ => (1 + 2 / ((4 : ℝ) * m + 1)) ^ m)
    Filter.atTop (nhds (Real.exp (1 / 2))) :=
  Real.tendsto_one_add_pow_exp_of_tendsto cat_mg_half

theorem cat_one_g : Filter.Tendsto (fun m : ℕ => (1 : ℝ) + 2 / ((4 : ℝ) * m + 1))
    Filter.atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add cat_g0
  simpa using h

theorem catRatio_lim : Filter.Tendsto
    (fun m : ℕ => ((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1))
    Filter.atTop (nhds (Real.exp 1)) := by
  have hF : Filter.Tendsto
      (fun m : ℕ => ((1 + 2 / ((4 : ℝ) * m + 1)) ^ m) ^ 2
        * (1 + 2 / ((4 : ℝ) * m + 1)))
      Filter.atTop (nhds ((Real.exp (1 / 2)) ^ 2 * 1)) :=
    (cat_pow_half.pow 2).mul cat_one_g
  have hexp1 : (Real.exp (1 / 2 : ℝ)) ^ 2 * 1 = Real.exp 1 := by
    rw [sq, ← Real.exp_add, mul_one,
      show (1 / 2 : ℝ) + 1 / 2 = 1 from by norm_num]
  rw [hexp1] at hF
  refine Filter.Tendsto.congr (fun m => ?_) hF
  have hb : (4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)
      = 1 + 2 / ((4 : ℝ) * m + 1) := by
    have h41 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [hb, ← pow_mul, ← pow_succ, show m * 2 + 1 = 2 * m + 1 from by ring]

end MetaMathlibExt
end
