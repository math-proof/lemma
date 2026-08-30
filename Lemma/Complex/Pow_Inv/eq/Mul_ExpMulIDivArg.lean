import sympy.Basic
import sympy.functions.elementary.complexes


@[main]
private lemma main
-- given
  (z : ℂ)
  (n : ℕ) :
-- imply
  z ^ (n : ℂ)⁻¹ = (‖z‖ : ℂ) ^ (n : ℂ)⁻¹ * (I * (arg z / (n : ℂ))).exp := by
-- proof
  if hn : n = 0 then
    subst hn
    simp [inv_zero, Complex.cpow_zero]
  else if hz : z = 0 then
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp [hz, hn']
  else
    have hnorm : (↑‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rw [Complex.cpow_def_of_ne_zero hz, Complex.cpow_def_of_ne_zero hnorm]
    rw [Complex.log]
    have hlog_norm : Complex.log (↑‖z‖) = ↑(Real.log ‖z‖) :=
      (Complex.ofReal_log (norm_nonneg z)).symm
    rw [hlog_norm, add_mul, Complex.exp_add]
    congr 1
    grind [mul_comm (arg z : ℂ) I]


-- created on 2018-08-22
-- updated on 2026-08-21
