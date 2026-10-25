import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Ex_3_8
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter3.Ex_3_8
open MeasureTheory Real Set intervalIntegral Chapter3


/--
[Icc_to_ii](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma Icc_to_ii
  {f : ℝ → ℝ} :
-- imply
  ∫ x in Icc (0 : ℝ) 1, f x = ∫ x in (0:ℝ)..1, f x := by
-- proof
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/--
[sin_2pi_m](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma sin_2pi_m
  {m : ℤ} :
-- imply
  sin (↑m * (2 * π)) = 0 := by
-- proof
  have := sin_int_mul_pi (2 * m)
  rw [show (↑(2 * m) : ℝ) * π = ↑m * (2 * π) from by push_cast; ring] at this; exact this

/--
[ics](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma ics
  {c : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, cos (c * x) = sin c / c := by
-- proof
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := c) (fun x => cos x) hc
  simp only [zero_mul, one_mul] at h; rw [integral_cos] at h
  rw [show (fun x : ℝ => cos (x * c)) = (fun x : ℝ => cos (c * x)) from by ext; ring_nf] at h
  rw [h]; simp [smul_eq_mul]; ring

/--
[iss](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma iss
  {c : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, sin (c * x) = (1 - cos c) / c := by
-- proof
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := c) (fun x => sin x) hc
  simp only [zero_mul, one_mul] at h; rw [integral_sin] at h
  rw [show (fun x : ℝ => sin (x * c)) = (fun x : ℝ => sin (c * x)) from by ext; ring_nf] at h
  rw [h]; simp [smul_eq_mul]; ring

/--
[two_pi_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma two_pi_ne
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  (2 : ℝ) * π * ↑m ≠ 0 :=
-- proof
  mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (Int.cast_ne_zero.mpr hm)

/--
[ic0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma ic0
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, cos (2 * π * m * x) = 0 := by
-- proof
  rw [ics _ (two_pi_ne m hm), show sin (2 * π * ↑m) = sin (↑m * (2 * π)) by ring, sin_2pi_m]; simp

/--
[is0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma is0
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, sin (2 * π * m * x) = 0 := by
-- proof
  rw [iss _ (two_pi_ne m hm), show cos (2 * π * ↑m) = cos (↑m * (2 * π)) by ring, cos_int_mul_two_pi]; simp

/--
[ics2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma ics2
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, cos (2 * π * m * x) ^ 2 = 1 / 2 := by
-- proof
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := 2 * π * m) (fun x => cos x ^ 2) (two_pi_ne m hm)
  simp only [zero_mul, one_mul] at h; rw [integral_cos_sq] at h
  rw [show (fun x : ℝ => cos (x * (2 * π * ↑m)) ^ 2) = (fun x : ℝ => cos (2 * π * ↑m * x) ^ 2) from by ext; ring_nf] at h
  rw [h]; simp only [smul_eq_mul, cos_zero, sin_zero]
  conv_lhs => rw [show (2 : ℝ) * π * ↑m = ↑m * (2 * π) from by ring]
  rw [sin_2pi_m, cos_int_mul_two_pi]; field_simp; ring

/--
[iss2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma iss2
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ∫ x in (0:ℝ)..1, sin (2 * π * m * x) ^ 2 = 1 / 2 := by
-- proof
  have h := @integral_comp_mul_right ℝ _ _ (a := 0) (b := 1) (c := 2 * π * m) (fun x => sin x ^ 2) (two_pi_ne m hm)
  simp only [zero_mul, one_mul] at h; rw [integral_sin_sq] at h
  rw [show (fun x : ℝ => sin (x * (2 * π * ↑m)) ^ 2) = (fun x : ℝ => sin (2 * π * ↑m * x) ^ 2) from by ext; ring_nf] at h
  rw [h]; simp only [smul_eq_mul, cos_zero, sin_zero]
  conv_lhs => rw [show (2 : ℝ) * π * ↑m = ↑m * (2 * π) from by ring]
  rw [sin_2pi_m, cos_int_mul_two_pi]; field_simp; ring

/--
[tb_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma tb_one
  {x : ℝ} :
-- imply
  trigBasis 1 x = 1 := by
-- proof
simp [trigBasis]

/--
[tb_even](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma tb_even
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 0 < m) :
-- imply
  trigBasis (2 * m) x = √2 * cos (2 * π * ↑m * x) := by
-- proof
  simp [trigBasis, show 2 * m ≠ 0 by omega, show 2 * m ≠ 1 by omega,
    show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]

/--
[tb_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma tb_odd
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 0 < m) :
-- imply
  trigBasis (2 * m + 1) x = √2 * sin (2 * π * ↑m * x) := by
-- proof
  unfold trigBasis
  simp only [show 2 * m + 1 ≠ 0 from by omega, ↓reduceIte,
    show ¬(2 * m + 1 = 1) from by omega,
    show ¬(2 * m + 1) % 2 = 0 from by omega,
    show (2 * m + 1 - 1) / 2 = m from by omega]

/--
[nat_tri](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma nat_tri
  {j : ℕ}
-- given
  (hj : 0 < j) :
-- imply
  j = 1 ∨ (∃ m, 0 < m ∧ j = 2 * m) ∨ (∃ m, 0 < m ∧ j = 2 * m + 1) := by
-- proof
  by_cases h1 : j = 1; · exact Or.inl h1
  right
  by_cases heven : j % 2 = 0
  · left; exact ⟨j / 2, by omega, by omega⟩
  · right; exact ⟨(j - 1) / 2, by omega, by omega⟩

/--
[icc0_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma icc0_nat
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n)
  (hmn : m ≠ n) :
-- imply
  ∫ x in (0:ℝ)..1, cos (2 * π * ↑m * x) * cos (2 * π * ↑n * x) = 0 := by
-- proof
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have h_sub_ne : (m : ℤ) - n ≠ 0 := by omega
  have key : (fun x : ℝ => cos (2 * π * ↑m * x) * cos (2 * π * ↑n * x)) =
    fun x => (cos (2 * π * ↑(m - n : ℤ) * x) + cos (2 * π * ↑(m + n : ℤ) * x)) / 2 := by
    ext x
    have h1 := cos_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := cos_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring,
      show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    ic0 _ h_sub_ne, ic0 _ h_sum_ne]; simp

/--
[iss0_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma iss0_nat
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n)
  (hmn : m ≠ n) :
-- imply
  ∫ x in (0:ℝ)..1, sin (2 * π * ↑m * x) * sin (2 * π * ↑n * x) = 0 := by
-- proof
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have h_sub_ne : (m : ℤ) - n ≠ 0 := by omega
  have key : (fun x : ℝ => sin (2 * π * ↑m * x) * sin (2 * π * ↑n * x)) =
    fun x => (cos (2 * π * ↑(m - n : ℤ) * x) - cos (2 * π * ↑(m + n : ℤ) * x)) / 2 := by
    ext x
    have h1 := cos_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := cos_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring,
      show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    ic0 _ h_sub_ne, ic0 _ h_sum_ne]; simp

/--
[isc0_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma isc0_nat
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  ∫ x in (0:ℝ)..1, sin (2 * π * ↑m * x) * cos (2 * π * ↑n * x) = 0 := by
-- proof
  have h_sum_ne : (m : ℤ) + n ≠ 0 := by omega
  have key : (fun x : ℝ => sin (2 * π * ↑m * x) * cos (2 * π * ↑n * x)) =
    fun x => (sin (2 * π * ↑(m + n : ℤ) * x) + sin (2 * π * ↑(m - n : ℤ) * x)) / 2 := by
    ext x
    have h1 := sin_add (2 * π * ↑m * x) (2 * π * ↑n * x)
    have h2 := sin_sub (2 * π * ↑m * x) (2 * π * ↑n * x)
    simp only [show 2 * π * (↑(m + n : ℤ) : ℝ) * x = 2 * π * ↑m * x + 2 * π * ↑n * x from by push_cast; ring,
      show 2 * π * (↑(m - n : ℤ) : ℝ) * x = 2 * π * ↑m * x - 2 * π * ↑n * x from by push_cast; ring]
    linarith
  rw [key, intervalIntegral.integral_div,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    is0 _ h_sum_ne]
  by_cases h_sub : (m : ℤ) - n = 0
  · rw [h_sub]; simp
  · rw [is0 _ h_sub]; simp

/--
[trigBasis_L2_orthonormal'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/TrigOrtho.lean)
-/
@[path]
lemma trigBasis_L2_orthonormal'
  {j k : ℕ}
-- given
  (hj : 0 < j)
  (hk : 0 < k) :
-- imply
  ∫ x in Icc (0 : ℝ) 1, trigBasis j x * trigBasis k x = if j = k then 1 else 0 := by
-- proof
  rw [Icc_to_ii]
  obtain rfl | ⟨mj, hmj, rfl⟩ | ⟨mj, hmj, rfl⟩ <;> := nat_tri j hj
  obtain rfl | ⟨mk, hmk, rfl⟩ | ⟨mk, hmk, rfl⟩ := nat_tri k hk
  · simp_rw [tb_one]; simp [intervalIntegral.integral_const]
  · simp only [show ¬(1 = 2 * mk) from by omega, ite_false]
    simp_rw [tb_one, tb_even mk hmk, one_mul, intervalIntegral.integral_const_mul]
    rw [show (fun x => cos (2 * π * ↑mk * x)) = (fun x => cos (2 * π * (↑(mk:ℤ)) * x)) from by push_cast; rfl]
    rw [ic0 mk (by exact_mod_cast show mk ≠ 0 by omega)]; simp
  · simp only [show ¬(1 = 2 * mk + 1) from by omega, ite_false]
    simp_rw [tb_one, tb_odd mk hmk, one_mul, intervalIntegral.integral_const_mul]
    rw [show (fun x => sin (2 * π * ↑mk * x)) = (fun x => sin (2 * π * (↑(mk:ℤ)) * x)) from by push_cast; rfl]
    rw [is0 mk (by exact_mod_cast show mk ≠ 0 by omega)]; simp
  · simp only [show ¬(2 * mj = 1) from by omega, ite_false]
    simp_rw [tb_even mj hmj, tb_one, mul_one, intervalIntegral.integral_const_mul]
    rw [show (fun x => cos (2 * π * ↑mj * x)) = (fun x => cos (2 * π * (↑(mj:ℤ)) * x)) from by push_cast; rfl]
    rw [ic0 mj (by exact_mod_cast show mj ≠ 0 by omega)]; simp
  · simp_rw [tb_even mj hmj, tb_even mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * cos (2 * π * ↑mj * x) * (√2 * cos (2 * π * ↑mk * x)) =
      √2 * √2 * (cos (2 * π * ↑mj * x) * cos (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul]
    by_cases h : mj = mk
    · subst h; simp only [show 2 * mj = 2 * mj from rfl, ite_true]
      rw [show (fun x : ℝ => cos (2 * π * ↑mj * x) * cos (2 * π * ↑mj * x)) =
        (fun x => cos (2 * π * ↑(mj:ℤ) * x) ^ 2) from by ext x; push_cast; ring]
      rw [ics2 mj (by exact_mod_cast show mj ≠ 0 by omega)]
      rw [Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]; ring
    · simp only [show ¬(2 * mj = 2 * mk) from by omega, ite_false]
      rw [icc0_nat mj mk hmj hmk h]; simp
  · simp only [show ¬(2 * mj = 2 * mk + 1) from by omega, ite_false]
    simp_rw [tb_even mj hmj, tb_odd mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * cos (2 * π * ↑mj * x) * (√2 * sin (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mk * x) * cos (2 * π * ↑mj * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul, isc0_nat mk mj hmk hmj]; simp
  · simp only [show ¬(2 * mj + 1 = 1) from by omega, ite_false]
    simp_rw [tb_odd mj hmj, tb_one, mul_one, intervalIntegral.integral_const_mul]
    rw [show (fun x => sin (2 * π * ↑mj * x)) = (fun x => sin (2 * π * (↑(mj:ℤ)) * x)) from by push_cast; rfl]
    rw [is0 mj (by exact_mod_cast show mj ≠ 0 by omega)]; simp
  · simp only [show ¬(2 * mj + 1 = 2 * mk) from by omega, ite_false]
    simp_rw [tb_odd mj hmj, tb_even mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * sin (2 * π * ↑mj * x) * (√2 * cos (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mj * x) * cos (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul, isc0_nat mj mk hmj hmk]; simp
  · simp_rw [tb_odd mj hmj, tb_odd mk hmk]
    simp_rw [show ∀ x : ℝ, √2 * sin (2 * π * ↑mj * x) * (√2 * sin (2 * π * ↑mk * x)) =
      √2 * √2 * (sin (2 * π * ↑mj * x) * sin (2 * π * ↑mk * x)) from fun x => by ring]
    rw [intervalIntegral.integral_const_mul]
    by_cases h : mj = mk
    · subst h; simp only [show 2 * mj + 1 = 2 * mj + 1 from rfl, ite_true]
      rw [show (fun x : ℝ => sin (2 * π * ↑mj * x) * sin (2 * π * ↑mj * x)) =
        (fun x => sin (2 * π * ↑(mj:ℤ) * x) ^ 2) from by ext x; push_cast; ring]
      rw [iss2 mj (by exact_mod_cast show mj ≠ 0 by omega)]
      rw [Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]; ring
    · simp only [show ¬(2 * mj + 1 = 2 * mk + 1) from by omega, ite_false]
      rw [iss0_nat mj mk hmj hmk h]; simp


-- created on 2026-10-23
