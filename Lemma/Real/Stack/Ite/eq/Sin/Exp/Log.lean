import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.DivMod
import sympy.Basic


@[path]
private lemma main
  {b : ℝ} {d i j : ℤ}
  (h₀ : 0 < b) :
-- imply
  (if j % 2 = 0 then
      Real.sin ((i : ℝ) * b ^ (-((j : ℝ) / (d : ℝ))))
    else
      Real.cos ((i : ℝ) * b ^ (-(((j - 1 : ℤ) : ℝ) / (d : ℝ))))) =
    Real.sin (Real.pi / 2 * ((j % 2 : ℤ) : ℝ) +
      (i : ℝ) * Real.exp (-(((2 * (j / 2) : ℤ) : ℝ) / (d : ℝ)) * Real.log b)) := by
-- proof
  have hexp : Real.exp (-(((2 * (j / 2) : ℤ) : ℝ) / (d : ℝ)) * Real.log b) =
      b ^ (-(((2 * (j / 2) : ℤ) : ℝ) / (d : ℝ))) := by
    rw [Real.rpow_def_of_pos h₀]
    ring_nf
  rw [hexp]
  have hrepr : j % 2 + (2 : ℤ) * (j / 2) = j := Int.emod_add_mul_ediv j 2
  if h : j % 2 = 0 then
    rw [ite_eq_left h]
    have hj : (j : ℝ) = ((2 * (j / 2) : ℤ) : ℝ) := by
      have hr : j = 2 * (j / 2) := by simpa [h, zero_add] using hrepr.symm
      exact_mod_cast hr
    rw [h, Int.cast_zero, mul_zero, zero_add]
    apply congrArg Real.sin
    apply congrArg (fun t : ℝ => (i : ℝ) * t)
    apply congrArg (fun e : ℝ => b ^ (-e))
    rw [hj]
  else
    rw [ite_eq_right h]
    have hmod : j % 2 = 1 := by
      obtain h0 | h1 := Int.emod_two_eq_zero_or_one j
      · exact absurd h0 h
      · exact h1
    have hj : ((j - 1 : ℤ) : ℝ) = ((2 * (j / 2) : ℤ) : ℝ) := by
      have hr := hrepr
      rw [hmod] at hr
      exact_mod_cast (show j - 1 = 2 * (j / 2) by linarith)
    rw [hmod, Int.cast_one, mul_one, add_comm]
    apply Eq.symm
    rw [hj]
    apply Real.sin_add_pi_div_two


-- created on 2026-10-11
-- updated on 2026-10-17
