import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Problem_3_4
open MeasureTheory Real Set


/--
[trigBasis_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Problem_3_4.lean)
-/
@[path]
lemma trigBasis_one
  {x : ℝ} :
-- imply
  trigBasis 1 x = 1 :=
-- proof
  rfl

/--
[trigBasis_of_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Problem_3_4.lean)
-/
@[path]
lemma trigBasis_of_ge_two
  {j : ℕ}
  {x : ℝ}
-- given
  (hj : 2 ≤ j) :
-- imply
  trigBasis j x = if j % 2 = 0 then √2 * cos (2 * π * (j / 2 : ℕ) * x) else √2 * sin (2 * π * ((j - 1) / 2 : ℕ) * x) := by
-- proof
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  simp only [trigBasis]
  have h1 : (n + 1) / 2 = (n + 2 - 1) / 2 := by omega
  split_ifs <;> simp_all

/--
[trigBasis_orthonormal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Problem_3_4.lean)
-/
@[path]
lemma trigBasis_orthonormal
  {j k : ℕ}
-- given
  (hj : 0 < j)
  (hk : 0 < k) :
-- imply
  ∫ x in (0 : ℝ)..1, trigBasis j x * trigBasis k x = if j = k then 1 else 0 := by
-- proof
  have int_cos_period : ∀ n : ℤ, n ≠ 0 →
    ∫ x in (0:ℝ)..1, cos (2 * π * ↑n * x) = 0 := by
    intro n hn
    have hc : (2 * π * (↑n : ℝ)) ≠ 0 := by
      apply mul_ne_zero; exact mul_ne_zero two_ne_zero pi_ne_zero; exact_mod_cast hn
    have heq : (fun x : ℝ => cos (2 * π * ↑n * x)) = (fun x => cos ((2 * π * ↑n) * x)) := by
      ext; ring_nf
    rw [heq, intervalIntegral.integral_comp_mul_left _ hc, mul_zero, mul_one, integral_cos,
      show 2 * π * (↑n : ℝ) = ↑(2 * n) * π from by push_cast; ring, sin_int_mul_pi,
      sin_zero, sub_self, smul_zero]
  have int_sin_period : ∀ n : ℤ, n ≠ 0 →
    ∫ x in (0:ℝ)..1, sin (2 * π * ↑n * x) = 0 := by
    intro n hn
    have hc : (2 * π * (↑n : ℝ)) ≠ 0 := by
      apply mul_ne_zero; exact mul_ne_zero two_ne_zero pi_ne_zero; exact_mod_cast hn
    have heq : (fun x : ℝ => sin (2 * π * ↑n * x)) = (fun x => sin ((2 * π * ↑n) * x)) := by
      ext; ring_nf
    rw [heq, intervalIntegral.integral_comp_mul_left _ hc, mul_zero, mul_one, integral_sin]
    simp only [show 2 * π * (↑n : ℝ) = ↑n * (2 * π) from by ring, cos_int_mul_two_pi,
      cos_zero, sub_self, smul_zero]
  have int_cos_cos : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∫ x in (0:ℝ)..1, cos (2 * π * ↑a * x) * cos (2 * π * ↑b * x) =
      if a = b then 1/2 else 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => cos (2 * π * ↑a * x) * cos (2 * π * ↑b * x)) =
      (fun x => (cos (2 * π * (↑a - ↑b : ℤ) * x) + cos (2 * π * (↑a + ↑b : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_cos_mul_cos (2 * π * ↑a * x) (2 * π * ↑b * x)
      have h1 : cos (2 * π * (↑a - ↑b : ℤ) * x) = cos (2 * π * ↑a * x - 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      have h2 : cos (2 * π * (↑a + ↑b : ℤ) * x) = cos (2 * π * ↑a * x + 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_add
        ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _),
      int_cos_period _ (by omega : (↑a + ↑b : ℤ) ≠ 0), add_zero]
    split_ifs with h
    · subst h; simp [sub_self, intervalIntegral.integral_const]
    · rw [int_cos_period _ (by omega : (↑a - ↑b : ℤ) ≠ 0), zero_div]
  have int_sin_sin : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∫ x in (0:ℝ)..1, sin (2 * π * ↑a * x) * sin (2 * π * ↑b * x) =
      if a = b then 1/2 else 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => sin (2 * π * ↑a * x) * sin (2 * π * ↑b * x)) =
      (fun x => (cos (2 * π * (↑a - ↑b : ℤ) * x) - cos (2 * π * (↑a + ↑b : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_sin_mul_sin (2 * π * ↑a * x) (2 * π * ↑b * x)
      have h1 : cos (2 * π * (↑a - ↑b : ℤ) * x) = cos (2 * π * ↑a * x - 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      have h2 : cos (2 * π * (↑a + ↑b : ℤ) * x) = cos (2 * π * ↑a * x + 2 * π * ↑b * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_sub
        ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _),
      int_cos_period _ (by omega : (↑a + ↑b : ℤ) ≠ 0), sub_zero]
    split_ifs with h
    · subst h; simp [sub_self, intervalIntegral.integral_const]
    · rw [int_cos_period _ (by omega : (↑a - ↑b : ℤ) ≠ 0), zero_div]
  have int_cos_sin : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∫ x in (0:ℝ)..1, cos (2 * π * ↑a * x) * sin (2 * π * ↑b * x) = 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => cos (2 * π * ↑a * x) * sin (2 * π * ↑b * x)) =
      (fun x => (sin (2 * π * (↑b - ↑a : ℤ) * x) + sin (2 * π * (↑b + ↑a : ℤ) * x)) / 2) := by
      ext x
      have := two_mul_sin_mul_cos (2 * π * ↑b * x) (2 * π * ↑a * x)
      have h1 : sin (2 * π * (↑b - ↑a : ℤ) * x) = sin (2 * π * ↑b * x - 2 * π * ↑a * x) := by
        congr 1; push_cast; ring
      have h2 : sin (2 * π * (↑b + ↑a : ℤ) * x) = sin (2 * π * ↑b * x + 2 * π * ↑a * x) := by
        congr 1; push_cast; ring
      rw [h1, h2]; linarith
    rw [heq, intervalIntegral.integral_div,
      intervalIntegral.integral_add
        ((by fun_prop : Continuous _).intervalIntegrable _ _)
        ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    by_cases hab : (↑b - ↑a : ℤ) = 0
    · rw [int_sin_period _ (by omega : (↑b + ↑a : ℤ) ≠ 0)]
      simp only [hab, Int.cast_zero, mul_zero, zero_mul, sin_zero,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul, zero_add, zero_div]
    · rw [int_sin_period _ hab, int_sin_period _ (by omega : (↑b + ↑a : ℤ) ≠ 0),
      zero_add, zero_div]
  have int_sin_cos : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    ∫ x in (0:ℝ)..1, sin (2 * π * ↑a * x) * cos (2 * π * ↑b * x) = 0 := by
    intro a b ha hb
    have heq : (fun x : ℝ => sin (2 * π * ↑a * x) * cos (2 * π * ↑b * x)) =
      (fun x => cos (2 * π * ↑b * x) * sin (2 * π * ↑a * x)) := by ext x; ring
    rw [heq, int_cos_sin b a hb ha]
  have sqrt2_sq : (√2 : ℝ) * √2 = 2 := by rw [← sq, sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
  obtain rfl | hj2 := Nat.eq_or_lt_of_le hj
  ·
    obtain rfl | hk2 := Nat.eq_or_lt_of_le hk
    ·
      simp [trigBasis_one, intervalIntegral.integral_const]
    ·
      simp only [show (1 : ℕ) ≠ k by omega, ite_false]
      simp_rw [trigBasis_one, one_mul, trigBasis_of_ge_two k (by omega)]
      split_ifs with hke
      · rw [intervalIntegral.integral_const_mul,
        show (↑(k / 2 : ℕ) : ℝ) = ((↑(k / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
        int_cos_period ↑(k / 2 : ℕ) (by omega), mul_zero]
      · rw [intervalIntegral.integral_const_mul,
        show (↑((k - 1) / 2 : ℕ) : ℝ) = ((↑((k - 1) / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
        int_sin_period ↑((k - 1) / 2 : ℕ) (by omega), mul_zero]
  ·
    obtain rfl | hk2 := Nat.eq_or_lt_of_le hk
    ·
      simp only [show j ≠ 1 by omega, ite_false]
      simp_rw [trigBasis_one, trigBasis_of_ge_two j (by omega)]
      split_ifs with hje
      · simp only [mul_one]
        rw [intervalIntegral.integral_const_mul,
          show (↑(j / 2 : ℕ) : ℝ) = ((↑(j / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
          int_cos_period ↑(j / 2 : ℕ) (by omega), mul_zero]
      · simp only [mul_one]
        rw [intervalIntegral.integral_const_mul,
          show (↑((j - 1) / 2 : ℕ) : ℝ) = ((↑((j - 1) / 2 : ℕ) : ℤ) : ℝ) from by push_cast; rfl,
          int_sin_period ↑((j - 1) / 2 : ℕ) (by omega), mul_zero]
    ·
      simp_rw [trigBasis_of_ge_two j (by omega), trigBasis_of_ge_two k (by omega)]
      by_cases hje : j % 2 = 0
      ·
        simp only [hje, ite_true]
        by_cases hke : k % 2 = 0
        ·
          simp only [hke, ite_true]
          have heq : (fun x : ℝ => √2 * cos (2 * π * ↑(j / 2) * x) *
            (√2 * cos (2 * π * ↑(k / 2) * x))) =
            (fun x => 2 * (cos (2 * π * ↑(j / 2) * x) * cos (2 * π * ↑(k / 2) * x))) := by
            ext x; rw [show √2 * cos (2 * π * ↑(j / 2) * x) *
              (√2 * cos (2 * π * ↑(k / 2) * x)) =
              (√2 * √2) * (cos (2 * π * ↑(j / 2) * x) *
              cos (2 * π * ↑(k / 2) * x)) from by ring, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
            int_cos_cos _ _ (by omega) (by omega)]
          split_ifs with hab hjk
          · norm_num
          · exfalso; exact hjk (by omega)
          · exfalso; exact hab (by omega)
          · norm_num
        ·
          simp only [show ¬(k % 2 = 0) from hke, ite_false]
          have heq : (fun x : ℝ => √2 * cos (2 * π * ↑(j / 2) * x) *
            (√2 * sin (2 * π * ↑((k - 1) / 2) * x))) =
            (fun x => 2 * (cos (2 * π * ↑(j / 2) * x) *
            sin (2 * π * ↑((k - 1) / 2) * x))) := by
            ext x
            rw [show √2 * cos _ * (√2 * sin _) = (√2 * √2) * (cos _ * sin _) from by ring,
              sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
            int_cos_sin _ _ (by omega) (by omega), mul_zero,
            if_neg (show ¬(j = k) from by omega)]
      ·
        simp only [show ¬(j % 2 = 0) from hje, ite_false]
        by_cases hke : k % 2 = 0
        ·
          simp only [hke, ite_true]
          have heq : (fun x : ℝ => √2 * sin (2 * π * ↑((j - 1) / 2) * x) *
            (√2 * cos (2 * π * ↑(k / 2) * x))) =
            (fun x => 2 * (sin (2 * π * ↑((j - 1) / 2) * x) *
            cos (2 * π * ↑(k / 2) * x))) := by
            ext x
            rw [show √2 * sin _ * (√2 * cos _) = (√2 * √2) * (sin _ * cos _) from by ring,
              sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
            int_sin_cos _ _ (by omega) (by omega), mul_zero,
            if_neg (show ¬(j = k) from by omega)]
        ·
          simp only [show ¬(k % 2 = 0) from hke, ite_false]
          have heq : (fun x : ℝ => √2 * sin (2 * π * ↑((j - 1) / 2) * x) *
            (√2 * sin (2 * π * ↑((k - 1) / 2) * x))) =
            (fun x => 2 * (sin (2 * π * ↑((j - 1) / 2) * x) *
            sin (2 * π * ↑((k - 1) / 2) * x))) := by
            ext x
            have : √2 * sin (2 * π * ↑((j - 1) / 2) * x) *
              (√2 * sin (2 * π * ↑((k - 1) / 2) * x)) =
              (√2 * √2) * (sin (2 * π * ↑((j - 1) / 2) * x) *
              sin (2 * π * ↑((k - 1) / 2) * x)) := by ring
            rw [this, sqrt2_sq]
          rw [heq, intervalIntegral.integral_const_mul,
            int_sin_sin _ _ (by omega) (by omega)]
          split_ifs with hab hjk
          · norm_num
          · exfalso; exact hjk (by omega)
          · exfalso; exact hab (by omega)
          · norm_num
/-- Orthonormality of the Haar system on `[0,1]`:
`∫₀¹ ψ_{j,k}(x) ψ_{j',k'}(x) dx = δ_{(j,k),(j',k')}` for admissible indices. -/


-- created on 2026-10-23
