import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (h₀ : 0 < n) :
-- imply
  (∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x ^ (n - 1)) =
    Real.sqrt Real.pi * Real.Gamma ((n : ℝ) / 2) /
      (2 * Real.Gamma ((n : ℝ) / 2 + 1 / 2)) := by
-- proof
  have hpow (k : ℕ) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x ^ k) =
      Real.sqrt Real.pi * Real.Gamma ((k + 1 : ℝ) / 2) /
        (2 * Real.Gamma ((k + 2 : ℝ) / 2)) := by
    induction k using Nat.twoStepInduction with
    | zero =>
      simp only [pow_zero, integral_one, Nat.cast_zero]
      norm_num
      rw [Real.Gamma_one_half_eq]
      apply Eq.symm
      apply Real.mul_self_sqrt Real.pi_pos.le
    | one =>
      simp only [pow_one, integral_cos, Real.sin_zero, Real.sin_pi_div_two, Nat.cast_one]
      have hnum : Real.Gamma ((1 + 1) / 2) = 1 := by
        norm_num [Real.Gamma_one]
      have hden : Real.Gamma ((1 + 2) / 2) = Real.sqrt Real.pi / 2 := by
        have hshift : (1 + 2) / 2 = (1 : ℝ) / 2 + 1 := by
          norm_num
        rw [hshift, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
        ring
      rw [hnum, hden]
      field_simp
      ring
    | more k ih _ =>
      have hrec := integral_cos_pow (a := 0) (b := Real.pi / 2) k
      have hbnd :
        Real.cos (Real.pi / 2) ^ (k + 1) * Real.sin (Real.pi / 2) -
            Real.cos 0 ^ (k + 1) * Real.sin 0 = 0 := by
        simp [Real.cos_pi_div_two, Real.sin_zero]
      rw [hrec, hbnd, zero_div, zero_add, ih]
      have hnum :
        Real.Gamma ((↑(k + 2) + 1) / 2) =
          ((k + 1 : ℝ) / 2) * Real.Gamma ((k + 1 : ℝ) / 2) := by
        have hshift : (↑(k + 2) + 1) / 2 = (k + 1 : ℝ) / 2 + 1 := by
          push_cast
          ring
        rw [hshift]
        apply Real.Gamma_add_one
        positivity
      have hden :
        Real.Gamma ((↑(k + 2) + 2) / 2) =
          ((k + 2 : ℝ) / 2) * Real.Gamma ((k + 2 : ℝ) / 2) := by
        have hshift : (↑(k + 2) + 2) / 2 = (k + 2 : ℝ) / 2 + 1 := by
          push_cast
          ring
        rw [hshift]
        apply Real.Gamma_add_one
        positivity
      have hpos : (Real.Gamma ((k + 2 : ℝ) / 2)) ≠ 0 :=
        (Real.Gamma_pos_of_pos (by positivity)).ne'
      rw [hnum, hden]
      field_simp [hpos]
  rw [hpow (n - 1)]
  have hle : 1 ≤ n := h₀
  have h1 : (↑(n - 1) + 1) / 2 = (n : ℝ) / 2 := by
    rw [Nat.cast_sub hle, Nat.cast_one]
    ring
  have h2 : (↑(n - 1) + 2) / 2 = (n : ℝ) / 2 + 1 / 2 := by
    rw [Nat.cast_sub hle, Nat.cast_one]
    ring
  rw [h1, h2]


-- created on 2020-06-30
-- updated on 2026-10-17
