import Mathlib
import sympy.Basic
open Set Real

private lemma pi2_lt_10 : π^2 < 10 := by
  nlinarith [pi_lt_d4, pi_pos, sq_nonneg (π - 3)]

private lemma quad_neg (p : ℝ) (hp0 : 0 ≤ p) (hp10 : p < 10) : p^2 + 42 * p - 756 < 0 := by
  have h1 : p^2 ≤ 10 * p := by
    have h : p * p ≤ 10 * p := mul_le_mul_of_nonneg_right (le_of_lt hp10) hp0
    simpa [pow_two] using h
  have h2 : 10 * p < 100 := by
    have h : 10 * p < 10 * (10 : ℝ) := mul_lt_mul_of_pos_left hp10 (by norm_num)
    norm_num at h ⊢; exact h
  have h3 : 42 * p < 420 := by
    have h : 42 * p < 42 * (10 : ℝ) := mul_lt_mul_of_pos_left hp10 (by norm_num)
    norm_num at h ⊢; exact h
  linarith

private lemma Q'_neg (z : ℝ) : -1 / 6 + π^2 / 120 + 2 * z * (1 / 120 - π^2 / 5040) - 3 * z^2 / 5040 < 0 := by
  have hpi2 : π^2 < 10 := pi2_lt_10
  have hpi2_nonneg : 0 ≤ π^2 := by positivity
  have disc : (2 * (1 / 120 - π^2 / 5040))^2 - 4 * (-3 / 5040 : ℝ) * (-1 / 6 + π^2 / 120) < 0 := by
    have heq : (2 * (1 / 120 - π^2 / 5040))^2 - 4 * (-3 / 5040 : ℝ) * (-1 / 6 + π^2 / 120) =
        ((π^2)^2 + 42 * π^2 - 756) / 6350400 := by ring
    rw [heq]
    exact div_neg_of_neg_of_pos (quad_neg (π^2) hpi2_nonneg hpi2) (by norm_num)
  have h : -1 / 6 + π^2 / 120 + 2 * z * (1 / 120 - π^2 / 5040) - 3 * z^2 / 5040 =
      (-3 / 5040 : ℝ) * (z + (2 * (1 / 120 - π^2 / 5040)) / (2 * (-3 / 5040 : ℝ)))^2 -
      ((2 * (1 / 120 - π^2 / 5040))^2 - 4 * (-3 / 5040 : ℝ) * (-1 / 6 + π^2 / 120)) / (4 * (-3 / 5040 : ℝ)) := by ring
  rw [h]
  have hsq : 0 ≤ (z + (2 * (1 / 120 - π^2 / 5040)) / (2 * (-3 / 5040 : ℝ)))^2 := by positivity
  have hterm1 : (-3 / 5040 : ℝ) * (z + (2 * (1 / 120 - π^2 / 5040)) / (2 * (-3 / 5040 : ℝ)))^2 ≤ 0 := by nlinarith
  have hterm2 : 0 < ((2 * (1 / 120 - π^2 / 5040))^2 - 4 * (-3 / 5040 : ℝ) * (-1 / 6 + π^2 / 120)) / (4 * (-3 / 5040 : ℝ)) := by
    exact div_pos_of_neg_of_neg disc (by norm_num)
  linarith

private lemma Q_decr (z w : ℝ) (h : z ≤ w) :
  (2 - π^2 / 6) + z * (-1 / 6 + π^2 / 120) + z^2 * (1 / 120 - π^2 / 5040) - z^3 / 5040 ≥
  (2 - π^2 / 6) + w * (-1 / 6 + π^2 / 120) + w^2 * (1 / 120 - π^2 / 5040) - w^3 / 5040 := by
  set a := (-1 / 5040 : ℝ) with ha
  set b := (1 / 120 - π^2 / 5040 : ℝ) with hb
  set c := (-1 / 6 + π^2 / 120 : ℝ) with hc
  set d := (2 - π^2 / 6 : ℝ) with hd
  let Qz := a * z^3 + b * z^2 + c * z + d
  let Qw := a * w^3 + b * w^2 + c * w + d
  let S := a * (z^2 + z * w + w^2) + b * (z + w) + c
  have hQz : (2 - π^2 / 6) + z * (-1 / 6 + π^2 / 120) + z^2 * (1 / 120 - π^2 / 5040) - z^3 / 5040 = Qz := by
    simp; ring
  have hQw : (2 - π^2 / 6) + w * (-1 / 6 + π^2 / 120) + w^2 * (1 / 120 - π^2 / 5040) - w^3 / 5040 = Qw := by
    simp; ring
  rw [hQz, hQw]
  have hdiff : Qz - Qw = (z - w) * S := by ring
  have hS_eq : S = 3 * a * ((z + w) / 2)^2 + 2 * b * ((z + w) / 2) + c + a * (z - w)^2 / 4 := by ring
  have hQ'_mid : 3 * a * ((z + w) / 2)^2 + 2 * b * ((z + w) / 2) + c < 0 := by
    have hq : 3 * a * ((z + w) / 2)^2 + 2 * b * ((z + w) / 2) + c =
        -1 / 6 + π^2 / 120 + 2 * ((z + w) / 2) * (1 / 120 - π^2 / 5040) - 3 * ((z + w) / 2)^2 / 5040 := by
      simp [ha, hb, hc]; ring
    rw [hq]
    exact Q'_neg ((z + w) / 2)
  have ha_neg : a < 0 := by simp [ha]; norm_num
  have hsq : 0 ≤ (z - w)^2 := by positivity
  have h2 : a * (z - w)^2 / 4 ≤ 0 := by nlinarith
  have hS_neg : S < 0 := by
    rw [hS_eq]; linarith
  have h3 : (z - w) * S ≥ 0 := by
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hS_neg.le
  have h5 : Qz - Qw ≥ 0 := by linarith [hdiff]
  linarith

private lemma Q_end_pos : 0 < (2 - π^2 / 6) + (π^2 / 4) * (-1 / 6 + π^2 / 120) +
    (π^2 / 4)^2 * (1 / 120 - π^2 / 5040) - (π^2 / 4)^3 / 5040 := by
  nlinarith [pi2_lt_10, sq_nonneg (π^2 - 197 / 20), sq_nonneg (π^2 - 99 / 10)]

@[path]
lemma sin5_gt
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  sin t < t - t^3/6 + t^5/120 := by
-- proof
  let h (v : ℝ) : ℝ := v - v^3/6 + v^5/120 - sin v
  have hh_deriv (v : ℝ) : deriv h v = 1 - v^2/2 + v^4/24 - cos v := by
    simp (disch := fun_prop) [h]
    ring
  have hcos2 : ∀ (v : ℝ), 0 < v → cos v < 1 - v^2/2 + v^4/24 := by
    intro v hv
    let k (w : ℝ) : ℝ := 1 - w^2/2 + w^4/24 - cos w
    have hk_deriv (w : ℝ) : deriv k w = -w + w^3/6 + sin w := by
      simp (disch := fun_prop) [k]
      ring
    have hk_mono : StrictMonoOn k (Set.Ici (0 : ℝ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) (by fun_prop)
      intro z hz
      have hz_pos : 0 < z := by
        simpa [interior_Ici] using hz
      have h_pos : 0 < -z + z^3/6 + sin z := by
        have := sin_gt_sub_cube hz_pos
        linarith
      simpa [hk_deriv] using h_pos
    have hk0 : k 0 < k v := hk_mono (by simp) hv.le hv
    simpa [k, Real.cos_zero] using hk0
  have hh_mono : StrictMonoOn h (Set.Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) (by fun_prop)
    intro z hz
    have hz_pos : 0 < z := by simpa [interior_Ici] using hz
    have : cos z < 1 - z^2/2 + z^4/24 := hcos2 z hz_pos
    simpa [hh_deriv, sub_pos] using this
  have hh0 : h 0 < h t := hh_mono (by simp) ht.le ht
  simpa [h, Real.sin_zero] using hh0

private lemma sin7_lt_sin : ∀ (t : ℝ), 0 < t → t - t^3/6 + t^5/120 - t^7/5040 < sin t := by
  intro t ht
  let f (s : ℝ) : ℝ := sin s - (s - s^3/6 + s^5/120 - s^7/5040)
  have hf_deriv (s : ℝ) : deriv f s = cos s - (1 - s^2/2 + s^4/24 - s^6/720) := by
    simp (disch := fun_prop) [f]
    ring
  have hcos3 : ∀ (s : ℝ), 0 < s → 1 - s^2/2 + s^4/24 - s^6/720 < cos s := by
    intro s hs
    let g (u : ℝ) : ℝ := cos u - (1 - u^2/2 + u^4/24 - u^6/720)
    have hg_deriv (u : ℝ) : deriv g u = -sin u + u - u^3/6 + u^5/120 := by
      simp (disch := fun_prop) [g]
      ring
    have hg_mono : StrictMonoOn g (Set.Ici (0 : ℝ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) (by fun_prop)
      intro z hz
      have hz_pos : 0 < z := by simpa [interior_Ici] using hz
      have : sin z < z - z^3/6 + z^5/120 := sin5_gt (ht := hz_pos)
      have h_pos : 0 < -sin z + z - z^3/6 + z^5/120 := by linarith
      simpa [hg_deriv] using h_pos
    have hg0 : g 0 < g s := hg_mono (by simp) hs.le hs
    simpa [g, Real.cos_zero] using hg0
  have hf_mono : StrictMonoOn f (Set.Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) (by fun_prop)
    intro z hz
    have hz_pos : 0 < z := by simpa [interior_Ici] using hz
    have : 1 - z^2/2 + z^4/24 - z^6/720 < cos z := hcos3 z hz_pos
    simpa [hf_deriv, sub_pos] using this
  have hf0 : f 0 < f t := hf_mono (by simp) ht.le ht
  simpa [f, Real.sin_zero] using hf0

private lemma redheffer_aux {t : ℝ} (ht : 0 < t) (ht2 : t ≤ π / 2) :
  sin t > t * (π^2 - t^2) / (π^2 + t^2) := by
  have hsin_t : t - t^3/6 + t^5/120 - t^7/5040 < sin t := sin7_lt_sin t ht
  set y := t^2 with hy_def
  have hy_nonneg : 0 ≤ y := by positivity
  have hy_le : y ≤ π^2 / 4 := by
    have : t^2 ≤ (π / 2)^2 := by nlinarith
    nlinarith
  have hpoly : (2 - π^2 / 6) + y * (-1 / 6 + π^2 / 120) + y^2 * (1 / 120 - π^2 / 5040) - y^3 / 5040 ≥ 0 := by
    have hQ_decr := Q_decr y (π^2 / 4) hy_le
    have hQ_pos := Q_end_pos
    linarith
  have hmain : (t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2) - t * (π^2 - t^2) =
      t^3 * ((2 - π^2 / 6) + y * (-1 / 6 + π^2 / 120) + y^2 * (1 / 120 - π^2 / 5040) - y^3 / 5040) := by
    simp [hy_def]; ring
  have ht3_pos : 0 < t^3 := by positivity
  have hsub : (t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2) - t * (π^2 - t^2) ≥ 0 := by
    rw [hmain]
    exact mul_nonneg ht3_pos.le hpoly
  have hdenom : 0 < π^2 + t^2 := by positivity
  have hmain' : (t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2) ≥ t * (π^2 - t^2) := by
    linarith
  have h : t * (π^2 - t^2) / (π^2 + t^2) ≤ t - t^3/6 + t^5/120 - t^7/5040 := by
    have h5 : t * (π^2 - t^2) ≤ (t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2) := hmain'
    have h6 : t * (π^2 - t^2) / (π^2 + t^2) ≤
        ((t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2)) / (π^2 + t^2) :=
      div_le_div_of_nonneg_right h5 hdenom.le
    have h7 : ((t - t^3/6 + t^5/120 - t^7/5040) * (π^2 + t^2)) / (π^2 + t^2) =
        t - t^3/6 + t^5/120 - t^7/5040 := by
      field_simp [hdenom.ne']
    rwa [h7] at h6
  linarith

@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioo 0 π) :
-- imply
  sin x > x * (π ^ 2 - x ^ 2) / (π ^ 2 + x ^ 2) := by
-- proof
  have h1 : 0 < x := h.1
  have h2 : x < π := h.2
  if h3 : x ≤ π / 2 then
    exact redheffer_aux h1 h3
  else
    have h3' : π / 2 < x := by linarith
    set t := π - x with ht_def
    have ht_pos : 0 < t := by linarith
    have ht_le : t ≤ π / 2 := by linarith
    have hsym : sin t = sin x := by
      rw [ht_def]
      exact Real.sin_pi_sub x
    have hred_t : sin t > t * (π^2 - t^2) / (π^2 + t^2) := redheffer_aux ht_pos ht_le
    have hcmp : t * (π^2 - t^2) / (π^2 + t^2) > x * (π^2 - x^2) / (π^2 + x^2) := by
      have hden1 : 0 < π^2 + t^2 := by positivity
      have hden2 : 0 < π^2 + x^2 := by positivity
      have hfact : (t * (π^2 - t^2)) * (π^2 + x^2) - (x * (π^2 - x^2)) * (π^2 + t^2) =
          t^2 * (π - t)^2 * (π - 2 * t) := by
        have hx : x = π - t := by linarith [ht_def]
        rw [hx]
        ring
      have hpos : 0 < t^2 * (π - t)^2 * (π - 2 * t) := by
        have h1 : 0 < t := ht_pos
        have h2 : 0 < π - t := by linarith
        have h3 : 0 < π - 2 * t := by linarith
        positivity
      have hcross : (t * (π^2 - t^2)) * (π^2 + x^2) > (x * (π^2 - x^2)) * (π^2 + t^2) := by
        linarith [hfact, hpos]
      have hdiff : t * (π^2 - t^2) / (π^2 + t^2) - x * (π^2 - x^2) / (π^2 + x^2) > 0 := by
        have h4 : t * (π^2 - t^2) / (π^2 + t^2) - x * (π^2 - x^2) / (π^2 + x^2) =
            ((t * (π^2 - t^2)) * (π^2 + x^2) - (x * (π^2 - x^2)) * (π^2 + t^2)) /
              ((π^2 + t^2) * (π^2 + x^2)) := by
          field_simp [hden1.ne', hden2.ne']
        rw [h4]
        apply div_pos
        · linarith [hfact, hpos]
        · positivity
      linarith
    linarith [hsym, hred_t, hcmp]


-- created on 2026-10-07
