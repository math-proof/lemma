import Mathlib
import Lemma.Real.GtSin.of.In_Icc
import sympy.Basic
open Set Real

@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioo 0 π) :
-- imply
  x ^ 2 * (x + sin x) / (x - sin x) > π ^ 2 := by
-- proof
  have h1 : 0 < x := h.1
  have h2 : x < π := h.2
  have hred : sin x > x * (π ^ 2 - x ^ 2) / (π ^ 2 + x ^ 2) := GtSin.of.In_Icc h
  have hdenom1 : 0 < π ^ 2 + x ^ 2 := by positivity
  have hsin_pos : 0 < sin x := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hsin_lt_x : sin x < x := by
    if hgt : 1 < x then
      have hsin1 : sin x ≤ 1 := Real.sin_le_one x
      linarith
    else
      have hle : x ≤ 1 := by linarith
      have hsin5 : sin x < x - x ^ 3 / 6 + x ^ 5 / 120 :=
        GtSin.of.In_Icc.sin5_gt (ht := h1)
      have h9 : x - x ^ 3 / 6 + x ^ 5 / 120 < x := by
        have hx2 : x ^ 2 ≤ 1 := by nlinarith
        have hx3_pos : 0 < x ^ 3 := by positivity
        have h11 : x ^ 2 / 120 < (1 : ℝ) / 6 := by
          linarith [hx2]
        have h12 : x ^ 3 * (x ^ 2 / 120) < x ^ 3 * (1 / 6) := mul_lt_mul_of_pos_left h11 hx3_pos
        have h13 : x ^ 3 * (x ^ 2 / 120) = x ^ 5 / 120 := by ring
        have h14 : x ^ 3 * (1 / 6) = x ^ 3 / 6 := by ring
        rw [h13, h14] at h12
        linarith
      linarith
  have hdenom2 : 0 < x - sin x := by linarith
  have hmain : sin x * (π ^ 2 + x ^ 2) > x * (π ^ 2 - x ^ 2) := by
    have h : sin x * (π ^ 2 + x ^ 2) > (x * (π ^ 2 - x ^ 2) / (π ^ 2 + x ^ 2)) * (π ^ 2 + x ^ 2) :=
      mul_lt_mul_of_pos_right hred hdenom1
    have h2' : (x * (π ^ 2 - x ^ 2) / (π ^ 2 + x ^ 2)) * (π ^ 2 + x ^ 2) = x * (π ^ 2 - x ^ 2) := by
      field_simp [hdenom1.ne']
    rwa [h2'] at h
  have hfinal : x ^ 2 * (x + sin x) > π ^ 2 * (x - sin x) := by linarith
  have h5 : x ^ 2 * (x + sin x) / (x - sin x) > (π ^ 2 * (x - sin x)) / (x - sin x) :=
    div_lt_div_of_pos_right hfinal hdenom2
  have h6 : (π ^ 2 * (x - sin x)) / (x - sin x) = π ^ 2 := by
    field_simp [hdenom2.ne']
  rwa [h6] at h5

-- created on 2026-10-07
