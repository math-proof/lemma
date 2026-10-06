import Mathlib
import sympy.Basic


/--
[Polynomial_log_norm_coeff_le_logMahlerMeasure_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_log_norm_coeff_le_logMahlerMeasure_add.lean)
-/

private lemma  Polynomial.log_norm_coeff_le_logMahlerMeasure_add' {p : Polynomial ℂ} {k : ℕ}
    (hk : p.coeff k ≠ 0) :
    Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 := by
  have hp : p ≠ 0 := fun h ↦ hk (by simp [h])
  have hkn : k ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hk
  have hchoose : (0 : ℝ) < p.natDegree.choose k := by exact_mod_cast Nat.choose_pos hkn
  have h1 := p.norm_coeff_le_choose_mul_mahlerMeasure k
  have hM := p.mahlerMeasure_pos_of_ne_zero hp
  calc Real.log ‖p.coeff k‖
      ≤ Real.log (p.natDegree.choose k * p.mahlerMeasure) :=
        Real.log_le_log (norm_pos_iff.mpr hk) h1
    _ = Real.log (p.natDegree.choose k) + p.logMahlerMeasure := by
        rw [Real.log_mul hchoose.ne' hM.ne', p.logMahlerMeasure_eq_log_MahlerMeasure]
    _ ≤ p.natDegree * Real.log 2 + p.logMahlerMeasure := by
        gcongr
        rw [← Real.log_pow]
        exact Real.log_le_log hchoose (by exact_mod_cast Nat.choose_le_two_pow _ _)
    _ = _ := add_comm _ _
@[main]
private lemma main
  {p : Polynomial ℂ}
  {k : ℕ}
-- given
  (hk : p.coeff k ≠ 0) :
-- imply
  Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure + p.natDegree * Real.log 2 :=
-- proof
  Polynomial.log_norm_coeff_le_logMahlerMeasure_add' hk


-- created on 2026-10-05
