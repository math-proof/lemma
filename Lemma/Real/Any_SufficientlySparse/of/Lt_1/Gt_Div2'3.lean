import sympy.stats.step_size
import sympy.Basic
import Lemma.Anchors.SumRangeT.le.SumRangeTime
import Lemma.Real.RobbinsMonroInvPoly.of.Ge_1.Le_1.Gt_Div1'2
import Lemma.Real.SumRangeInvPoly.le.DivSubPow.of.Lt_1.Ge_0
open Finset Real


@[main]
private lemma main
  {ν : ℝ}
-- given
  (h₀ : 2 / 3 < ν)
  (h₁ : ν < 1) :
-- imply
  ∃ anc : Anchors (fun n : ℕ => inv_poly ν 2 n), SufficientlySparse anc := by
-- proof
  set z := ν / (2 - ν) with hz
  have h2ν : 0 < 2 - ν := by linarith
  have h1ν : 0 < 1 - ν := by linarith
  have hz_gt : 1 / 2 < z := by rw [hz, lt_div_iff₀ h2ν]; linarith
  have hz_lt : z < 1 := by rw [hz, div_lt_one h2ν]; linarith
  let anc : Anchors (fun n : ℕ => inv_poly ν 2 n) :=
    { hα := RobbinsMonroInvPoly.of.Ge_1.Le_1.Gt_Div1'2 (by linarith) h₁.le (by norm_num)
      hα_mono := fun x y hxy => by
        simp only [inv_poly]
        have : (x : ℝ) ≤ y := by exact_mod_cast hxy
        exact rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      T := fun n => inv_poly z 1 n
      hT := RobbinsMonroInvPoly.of.Ge_1.Le_1.Gt_Div1'2 hz_gt hz_lt.le le_rfl }
  refine ⟨anc, ?_⟩
  set r := ν / (1 - ν) with hr_def
  have hr : 0 < r := div_pos (by linarith) h1ν
  have hzr : (1 - z) * r = 2 * z := by
    rw [hz, hr_def]
    field_simp
    ring
  set c := (1 - ν) ^ (-r)
  have hc : 0 < c := rpow_pos_of_pos h1ν _
  refine ⟨max 1 (4 * c), by positivity, fun n => ?_⟩
  show inv_poly ν 2 (anc.t n : ℝ) ≤ _
  have hT : 0 < anc.T n := rpow_pos_of_pos (by positivity) _
  have hTβ := Anchors.T.le.β (anc := anc) (n := n)
  have hTβ2 : anc.T n ^ 2 ≤ anc.β n ^ 2 := pow_le_pow_left₀ hT.le hTβ 2
  have hT2 : anc.T n ^ 2 = ((n : ℝ) + 1) ^ (-(2 * z)) := by
    show ((((n : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) ^ (-z)) ^ 2 = _
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    push_cast
    ring_nf
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hTβ2 (by positivity))
  rw [hT2]
  if hn : n = 0 then
    subst hn
    rw [anc.t_zero]
    simp only [inv_poly, Nat.cast_zero, zero_add, one_rpow, mul_one]
    calc ((2 : ℕ) : ℝ) ^ (-ν) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      _ ≤ _ := le_max_left _ _
  else
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hlow : (n : ℝ) ^ (1 - z) ≤ ∑ k ∈ range n, anc.T k := by
      calc (n : ℝ) ^ (1 - z) = ∑ k ∈ range n, (n : ℝ) ^ (-z) := by
            rw [sum_const, card_range, nsmul_eq_mul, sub_eq_add_neg, rpow_add (by linarith), rpow_one]
        _ ≤ _ := sum_le_sum fun k hk => by
            show _ ≤ (((k : ℕ) : ℝ) + ((1 : ℕ) : ℝ)) ^ (-z)
            have : (k : ℝ) + 1 ≤ n := by
              have := mem_range.mp hk
              exact_mod_cast this
            push_cast
            exact rpow_le_rpow_of_nonpos (by positivity) this (by linarith)
    have hup := SumRangeInvPoly.le.DivSubPow.of.Lt_1.Ge_0 (a := anc.t n) (by linarith) h₁
    have hsum := Anchors.SumRangeT.le.SumRangeTime (anc := anc) (m := n)
    have hkey : (1 - ν) * (n : ℝ) ^ (1 - z) ≤ ((anc.t n : ℝ) + 1) ^ (1 - ν) := by
      have := hlow.trans (hsum.trans hup)
      rw [le_div_iff₀ h1ν] at this
      linarith
    have hA : 0 < (1 - ν) * (n : ℝ) ^ (1 - z) := by positivity
    have hpow := rpow_le_rpow_of_nonpos hA hkey (by linarith : -r ≤ 0)
    rw [← rpow_mul (by positivity), mul_rpow h1ν.le (by positivity), ← rpow_mul (by positivity)] at hpow
    have e1 : (1 - ν) * -r = -ν := by
      rw [hr_def]
      field_simp
    have e2 : (1 - z) * -r = -(2 * z) := by rw [mul_neg, hzr]
    rw [e1, e2] at hpow
    have hα : inv_poly ν 2 (anc.t n : ℝ) ≤ ((anc.t n : ℝ) + 1) ^ (-ν) := by
      simp only [inv_poly]
      push_cast
      exact rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hn2 : (n : ℝ) ^ (-(2 * z)) ≤ 4 * ((n : ℝ) + 1) ^ (-(2 * z)) := by
      have h2n : (n : ℝ) + 1 ≤ 2 * n := by linarith
      have h := rpow_le_rpow_of_nonpos (by positivity) h2n (by linarith : -(2 * z) ≤ 0)
      rw [mul_rpow (by norm_num) (by positivity)] at h
      have h4 : (2 : ℝ) ^ (-(2 : ℝ)) ≤ 2 ^ (-(2 * z)) :=
        rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h4' : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
        rw [rpow_neg (by norm_num)]
        norm_num
      rw [h4'] at h4
      nlinarith [rpow_pos_of_pos (by positivity : (0 : ℝ) < n) (-(2 * z))]
    calc inv_poly ν 2 (anc.t n : ℝ) ≤ c * (n : ℝ) ^ (-(2 * z)) := hα.trans hpow
      _ ≤ c * (4 * ((n : ℝ) + 1) ^ (-(2 * z))) := mul_le_mul_of_nonneg_left hn2 hc.le
      _ = 4 * c * ((n : ℝ) + 1) ^ (-(2 * z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


-- created on 2026-09-26