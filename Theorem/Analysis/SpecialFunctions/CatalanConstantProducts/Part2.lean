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
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part2


section

namespace MetaMathlibExt

/-- The three new factors combine into the boundary-factor ratio. -/
theorem key (m : ℕ) : catF (2 * m + 1) * (catF (2 * m + 2)) ^ 2 * catF (2 * m + 3)
    = (4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
      ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7)) := by
  rw [catF_succ_odd, catF_succ_even, catF_succ_odd3]
  simp only [div_pow]
  have h1 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * (m : ℝ) + 3 := by positivity
  have h5 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by positivity
  have h7 : (0 : ℝ) < 4 * (m : ℝ) + 7 := by positivity
  have n1 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := ne_of_gt h1
  have n3 : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := ne_of_gt h3
  have n5 : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := ne_of_gt h5
  have n7 : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := ne_of_gt h7
  field_simp
  ring

theorem catPm_step (m : ℕ) :
    catP (m + 1) = catP m * catF (2 * m + 1) * catF (2 * m + 2) := by
  have h := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (f := catF) (by omega)
  rw [show (2 * m + 1) + 1 = 2 * m + 2 from by omega] at h
  have h2 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m) (f := catF) (by omega)
  unfold catP
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring, h, h2]

theorem catQm_step (m : ℕ) :
    catQ (m + 1) = catQ m * catF (2 * m + 2) * catF (2 * m + 3) := by
  have h1 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 2) (f := catF) (by omega)
  rw [show (2 * m + 2) + 1 = 2 * m + 3 from by omega] at h1
  have h2 := Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (f := catF) (by omega)
  rw [show (2 * m + 1) + 1 = 2 * m + 2 from by omega] at h2
  unfold catQ
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring, h1, h2]

theorem catPQ_step (m : ℕ) : catP (m + 1) * catQ (m + 1)
    = (catP m * catQ m) *
      ((4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
        ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7))) := by
  have hrw : catP (m + 1) * catQ (m + 1)
      = (catP m * catQ m) *
        (catF (2 * m + 1) * (catF (2 * m + 2)) ^ 2 * catF (2 * m + 3)) := by
    rw [catPm_step, catQm_step]
    ring
  rw [hrw, key]

theorem catR_step (m : ℕ) : catR (m + 1)
    = catR m *
      ((4 * (m : ℝ) + 3) ^ (6 * m + 5) * (4 * (m : ℝ) + 7) ^ (2 * m + 3) /
        ((4 * (m : ℝ) + 1) ^ (2 * m + 1) * (4 * (m : ℝ) + 5) ^ (6 * m + 7))) := by
  have hA : (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact pow_ne_zero _ (by positivity)
  have hB : (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact pow_ne_zero _ (by positivity)
  have h1 : (0 : ℝ) < 4 * (m : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 4 * (m : ℝ) + 3 := by positivity
  have h5 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by positivity
  have h7 : (0 : ℝ) < 4 * (m : ℝ) + 7 := by positivity
  have n1 : (4 : ℝ) * (m : ℝ) + 1 ≠ 0 := ne_of_gt h1
  have n3 : (4 : ℝ) * (m : ℝ) + 3 ≠ 0 := ne_of_gt h3
  have n5 : (4 : ℝ) * (m : ℝ) + 5 ≠ 0 := ne_of_gt h5
  have n7 : (4 : ℝ) * (m : ℝ) + 7 ≠ 0 := ne_of_gt h7
  unfold catR
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring,
    show 6 * (m + 1) + 1 = 6 * m + 7 from by ring,
    show (4 : ℝ) * (↑m + 1) + 3 = 4 * ↑m + 7 from by ring,
    show (4 : ℝ) * (↑m + 1) + 1 = 4 * ↑m + 5 from by ring]
  field_simp
  ring

/-- The third product equals the product of the first two, exactly. -/
theorem catR_eq (m : ℕ) : catR m = catP m * catQ m := by
  induction m with
  | zero =>
    unfold catR catP catQ catF
    simp
    norm_num
  | succ m ih =>
    rw [catR_step, catPQ_step, ih]

/-- The second limit follows from the first plus the boundary factor. -/
theorem catQ_of_catP (G : ℝ)
    (hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2)))) :
    Filter.Tendsto catQ Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi + 1 / 2))) := by
  have hQ : catQ = fun m =>
      catP m * (((4 * (m : ℝ) + 3) / (4 * (m : ℝ) + 1)) ^ (2 * m + 1)) :=
    funext fun m => catQ_eq m
  rw [hQ]
  have hlim := hP.mul catRatio_lim
  have hexp : Real.exp (2 * G / Real.pi - 1 / 2) * Real.exp 1
      = Real.exp (2 * G / Real.pi + 1 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hexp] at hlim

/-- The third limit follows from the first two. -/
theorem catR_of_catPQ (G : ℝ)
    (hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2))))
    (hQ : Filter.Tendsto catQ Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi + 1 / 2)))) :
    Filter.Tendsto catR Filter.atTop (nhds (Real.exp (4 * G / Real.pi))) := by
  have hR : catR = fun m => catP m * catQ m := funext fun m => catR_eq m
  rw [hR]
  have hlim := hP.mul hQ
  have hexp : Real.exp (2 * G / Real.pi - 1 / 2) *
      Real.exp (2 * G / Real.pi + 1 / 2) = Real.exp (4 * G / Real.pi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hexp] at hlim

/-- Positivity of each base factor for `n ≥ 1`. -/
theorem catBase_pos (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) < 1 - 2 / (2 * (n : ℝ) + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  have hnum : (0 : ℝ) < 2 * (n : ℝ) - 1 := by linarith
  have heq : (1 : ℝ) - 2 / (2 * (n : ℝ) + 1)
      = (2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  rw [heq]
  exact div_pos hnum hden

/-- Positivity of each factor. -/
theorem catF_pos (n : ℕ) (hn : 1 ≤ n) : 0 < catF n := by
  unfold catF
  exact zpow_pos (catBase_pos n hn) _

/-- Positivity of the first product. -/
theorem catP_pos (m : ℕ) : 0 < catP m := by
  unfold catP
  apply Finset.prod_pos
  intro n hn
  simp only [Finset.mem_Icc] at hn
  exact catF_pos n hn.1

/-- Log of the first product as a finite sum. -/
theorem catP_log (m : ℕ) : Real.log (catP m) =
    ∑ n ∈ Finset.Icc 1 (2 * m),
      (((n : ℤ) * (-1 : ℤ) ^ n : ℤ) : ℝ) * Real.log (1 - 2 / (2 * (n : ℝ) + 1)) := by
  unfold catP catF
  rw [Real.log_prod]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rw [Real.log_zpow]
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    exact ne_of_gt (catF_pos n hn.1)

/-- First limit from the log-sum limit via continuity of `exp`. -/
theorem catP_of_log (G : ℝ)
    (hlog : Filter.Tendsto (fun m : ℕ => Real.log (catP m))
      Filter.atTop (nhds (2 * G / Real.pi - 1 / 2))) :
    Filter.Tendsto catP Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) := by
  have hexp : Filter.Tendsto (fun m : ℕ => Real.exp (Real.log (catP m)))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) :=
    hlog.rexp
  refine Filter.Tendsto.congr (fun m => ?_) hexp
  rw [Real.exp_log (catP_pos m)]

/-- Derivative of the log-difference antiderivative. -/
theorem catInt_hasDerivAt (a u : ℝ) (ha : 2 ≤ a)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt (fun v : ℝ => Real.log (a + v) - Real.log (a - v))
      (1 / (a + u) + 1 / (a - u)) u := by
  have hpos1 : (0 : ℝ) < a + u := by linarith
  have hpos2 : (0 : ℝ) < a - u := by linarith
  have hne1 : a + u ≠ 0 := ne_of_gt hpos1
  have hne2 : a - u ≠ 0 := ne_of_gt hpos2
  have h1 : HasDerivAt (fun v : ℝ => a + v) 1 u := by
    have h := (hasDerivAt_id (x := u)).const_add a
    simpa only [id_eq] using h
  have h2 : HasDerivAt (fun v : ℝ => a - v) (-1) u := by
    have h := (hasDerivAt_id (x := u)).const_sub a
    simpa only [id_eq] using h
  have hl1 : HasDerivAt (fun v : ℝ => Real.log (a + v)) (1 / (a + u)) u :=
    h1.log hne1
  have hl2 : HasDerivAt (fun v : ℝ => Real.log (a - v)) ((-1) / (a - u)) u :=
    h2.log hne2
  have hsub := hl1.sub hl2
  refine hsub.congr_deriv ?_
  have heq : ((-1 : ℝ) / (a - u)) = -(1 / (a - u)) := by
    rw [neg_div]
  rw [heq, sub_neg_eq_add]

/-- Integral of `a^2/(a^2-u^2)` over `[0,1]`. -/
theorem catInt_integral (a : ℝ) (ha : 2 ≤ a) :
    (∫ u in (0 : ℝ)..1, a ^ 2 / (a ^ 2 - u ^ 2)) =
      (a / 2) * Real.log ((a + 1) / (a - 1)) := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_of_le (by norm_num)
  have hcont : ContinuousOn (fun u : ℝ => a ^ 2 / (a ^ 2 - u ^ 2))
      (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuousOn_const.sub (ContinuousOn.pow continuousOn_id 2))
    · intro u hu
      simp only [Set.mem_Icc] at hu
      have hub : u ^ 2 ≤ 1 := by
        have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
        calc u ^ 2 = |u| ^ 2 := by rw [sq_abs]
          _ ≤ 1 ^ 2 := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          _ = 1 := one_pow 2
      have ha2 : (2 : ℝ) ≤ a ^ 2 := by
        calc (2 : ℝ) ≤ a := ha
          _ ≤ a ^ 2 := by
              have h1 : (1 : ℝ) ≤ a := by linarith
              calc a = a * 1 := by rw [mul_one]
                _ ≤ a * a := by
                    apply mul_le_mul_of_nonneg_left h1 (by linarith)
                _ = a ^ 2 := by rw [pow_two]
      linarith
  have hint : IntervalIntegrable (fun u : ℝ => a ^ 2 / (a ^ 2 - u ^ 2))
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) (1 : ℝ),
      HasDerivAt (fun v : ℝ => (a / 2) * (Real.log (a + v) - Real.log (a - v)))
        (a ^ 2 / (a ^ 2 - u ^ 2)) u := by
    intro u hu
    rw [huIcc, Set.mem_Icc] at hu
    have hbase := catInt_hasDerivAt a u ha hu.1 hu.2
    have hmul := hbase.const_mul (a / 2)
    refine hmul.congr_deriv ?_
    have hpos1 : (0 : ℝ) < a + u := by linarith
    have hpos2 : (0 : ℝ) < a - u := by linarith
    have hne1 : a + u ≠ 0 := ne_of_gt hpos1
    have hne2 : a - u ≠ 0 := ne_of_gt hpos2
    have hne3 : a ^ 2 - u ^ 2 ≠ 0 := by
      have : a ^ 2 - u ^ 2 = (a + u) * (a - u) := by ring
      rw [this]
      exact mul_ne_zero hne1 hne2
    field_simp
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  have h0 : (a / 2) * (Real.log (a + (0 : ℝ)) - Real.log (a - (0 : ℝ))) = 0 := by
    simp only [add_zero, sub_zero, sub_self, mul_zero]
  rw [h0, sub_zero]
  have hlog : Real.log (a + (1 : ℝ)) - Real.log (a - (1 : ℝ))
      = Real.log ((a + 1) / (a - 1)) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [hlog]

end MetaMathlibExt
end
