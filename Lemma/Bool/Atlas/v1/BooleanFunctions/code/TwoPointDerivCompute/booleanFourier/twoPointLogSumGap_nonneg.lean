import Mathlib
import Notation.Algebra.Power
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointDerivCompute.booleanFourier.twoPointLogPathFn_deriv_decomp
open Real Set BooleanFourier Bool


/--
[twoPointLogSumGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointDerivCompute.lean)
-/
@[path]
private lemma main
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ha : a > 0)
  (hb : b > 0)
  (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
-- imply
  0 ≤ twoPointLogSumGap p a b t := by
-- proof
  unfold twoPointLogSumGap
  simp only
  set r := 1 + (p - 1) / t²
  set c := (1 + t) / 2 * a + (1 - t) / 2 * b
  set d := (1 - t) / 2 * a + (1 + t) / 2 * b
  set S := c ^ r + d ^ r
  have hr_pos : (0 : ℝ) < r := by
    have : 0 < (p - 1) / t² := div_pos (by linarith [hp]) (sq_pos_of_pos ht.1); linarith
  have hc_pos : (0 : ℝ) < c :=
    add_pos (mul_pos (by linarith [ht.1]) ha) (mul_pos (by linarith [ht.2]) hb)
  have hd_pos : (0 : ℝ) < d :=
    add_pos (mul_pos (by linarith [ht.2]) ha) (mul_pos (by linarith [ht.1]) hb)
  have hS_pos : (0 : ℝ) < S :=
    add_pos_of_pos_of_nonneg (rpow_pos_of_pos hc_pos r) (rpow_nonneg hd_pos.le r)
  set u := c ^ r
  set v := d ^ r
  have hu_pos : (0 : ℝ) < u := rpow_pos_of_pos hc_pos r
  have hv_pos : (0 : ℝ) < v := rpow_pos_of_pos hd_pos r
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  suffices h : (0 : ℝ) ≤ (u * Real.log u + v * Real.log v) / S -
    Real.log (S / 2) by
    have : c ^ r * Real.log c + d ^ r * Real.log d =
      1 / r * (u * Real.log u + v * Real.log v) := by
      have hlog_u : Real.log u = r * Real.log c := Real.log_rpow hc_pos r
      have hlog_v : Real.log v = r * Real.log d := Real.log_rpow hd_pos r
      simp only [u, v]
      rw [hlog_u, hlog_v]
      field_simp
    rw [this]
    have hS_eq_uv : S = u + v := rfl
    rw [show 1 / r * (u * Real.log u + v * Real.log v) / S - 1 / r * Real.log (S / 2) =
      1 / r * ((u * Real.log u + v * Real.log v) / S - Real.log (S / 2)) by ring]
    exact mul_nonneg (by positivity : (0:ℝ) ≤ 1/r) h
  have hconv := Real.convexOn_mul_log
  have hu_mem : u ∈ Set.Ici (0 : ℝ) := le_of_lt hu_pos
  have hv_mem : v ∈ Set.Ici (0 : ℝ) := le_of_lt hv_pos
  have hJ := hconv.2 hu_mem hv_mem (by linarith : (0:ℝ) ≤ 1/2)
    (by linarith : (0:ℝ) ≤ 1/2) (by ring : (1:ℝ)/2 + 1/2 = 1)
  simp only [smul_eq_mul] at hJ
  have h_avg : (1:ℝ)/2 * u + 1/2 * v = S / 2 := by simp [S]; ring
  rw [h_avg] at hJ
  have hrewrite : (u * Real.log u + v * Real.log v) / S - Real.log (S / 2) =
    ((u * Real.log u + v * Real.log v) / 2 - S / 2 * Real.log (S / 2)) / (S / 2) := by
    field_simp
  rw [hrewrite]
  apply div_nonneg _ (by linarith : (0:ℝ) ≤ S / 2)
  linarith


lemma BooleanFourier.twoPointLogSumGap_nonneg
  {p a b t : ℝ}
-- given
  (hp : p > 1)
  (ha : a > 0)
  (hb : b > 0)
  (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
-- imply
  0 ≤ twoPointLogSumGap p a b t :=
-- proof
  main hp ha hb ht


-- created on 2026-10-23
-- updated on 2026-11-24
