import Mathlib
import sympy.Basic


/--
[Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq.lean)
-/
@[path]
private lemma main
  {k r : ℝ}
  {s : ℂ}
-- given
  (hr : 0 < r)
  (hs : -k < s.re) :
-- imply
  MellinConvergent (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s ∧
    mellin (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s =
      (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ)) := by
-- proof
  have hre : 0 < (s + (k : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have key : ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (s + (k : ℂ) - 1) * Complex.exp (-((r : ℂ) * (t : ℂ))) =
      (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ)) :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hr
  have hcongr : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))))
      (fun t : ℝ => (t : ℂ) ^ (s + (k : ℂ) - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Set.Ioi 0) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    simp only [smul_eq_mul]
    rw [show s + (k : ℂ) - 1 = (s - 1) + (k : ℂ) by ring, Complex.cpow_add _ _ ht0]
    ring
  have hne : (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hre)
    have h1 : (1 / (r : ℂ)) ≠ 0 := one_div_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))
    rw [Complex.cpow_def_of_ne_zero h1]
    exact Complex.exp_ne_zero _
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s + (k : ℂ) - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Set.Ioi 0) :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [key]; exact hne)
  refine ⟨?_, ?_⟩
  · exact hint.congr_fun hcongr.symm measurableSet_Ioi
  · rw [mellin, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, key]


-- created on 2026-10-05
