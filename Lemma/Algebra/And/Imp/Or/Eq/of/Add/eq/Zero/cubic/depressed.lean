import sympy.functions.elementary.complexes
import sympy.core.power
import sympy.core.numbers
import sympy.Basic


@[main]
private lemma main
  {x p q A B : ℂ}
-- given
  (h : x ^ 3 + p * x + q = 0)
  (hAB : A ^ 3 + B ^ 3 = -q)
  (hp : 3 * A * B = -p) :
-- imply
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  x = A + B ∨ x = A * ω + B * (starRingEnd ℂ) ω ∨ x = A * (starRingEnd ℂ) ω + B * ω := by
-- proof
  intro ω
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hadd : ω + (starRingEnd ℂ) ω = -1 := by
    apply Complex.ext
    ·
      simp [Complex.add_re, Complex.conj_re, hre]
      ring
    ·
      simp [Complex.add_im, Complex.conj_im, him]
  have hsq : ω ^ 2 = (starRingEnd ℂ) ω := by
    apply Complex.ext
    ·
      simp [pow_two, Complex.mul_re, Complex.conj_re, hre, him]
      ring_nf
      rw [h3]
      ring
    ·
      simp [pow_two, Complex.mul_im, Complex.conj_im, hre, him]
      ring
  have hsq' : ((starRingEnd ℂ) ω) ^ 2 = ω := by
    apply Complex.ext
    ·
      simp [pow_two, Complex.mul_re, Complex.conj_re, hre, him]
      ring_nf
      rw [h3]
      ring
    ·
      simp [pow_two, Complex.mul_im, Complex.conj_im, hre, him]
      ring
  have hcube : ω ^ 3 = 1 := by
    apply Complex.ext
    ·
      simp [pow_succ, Complex.mul_re, hre, him]
      ring_nf
      rw [h3]
      ring
    ·
      simp [pow_succ, Complex.mul_im, hre, him]
      field_simp
      rw [h3]
      ring
  have hmul : ω * (starRingEnd ℂ) ω = 1 := by
    rw [Complex.mul_conj, Complex.normSq_apply, hre, him]
    ring_nf
    rw [h3]
    norm_num
  have hc3 : ((starRingEnd ℂ) ω) ^ 3 = 1 := by
    rw [pow_succ, hsq', hmul]
  have hc4 : ((starRingEnd ℂ) ω) ^ 4 = (starRingEnd ℂ) ω := by
    rw [pow_succ, hc3, one_mul]
  have hc6 : ((starRingEnd ℂ) ω) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, hc3, mul_one]
  have hc8 : ((starRingEnd ℂ) ω) ^ 8 = ((starRingEnd ℂ) ω) ^ 2 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, pow_add, hc6, one_mul]
  have hx3 : x ^ 3 + p * x + q = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
    rw [hp, hAB]
    ring
  have hprod : (x - (A + B)) * (x - (A * ω + B * (starRingEnd ℂ) ω)) * (x - (A * (starRingEnd ℂ) ω + B * ω)) = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
    rw [← hsq, ← hsq']
    ring_nf
    rw [hc8, hc6, hc4, hsq']
    simp only [mul_one]
    have hstar : (starRingEnd ℂ) ω = -1 - ω := eq_sub_of_add_eq (by rwa [add_comm])
    rw [hstar]
    ring
  have h0 : (x - (A + B)) * (x - (A * ω + B * (starRingEnd ℂ) ω)) * (x - (A * (starRingEnd ℂ) ω + B * ω)) = 0 := by
    rw [hprod, ← hx3, h]
  rcases mul_eq_zero.mp h0 with h0 | h0
  ·
    rcases mul_eq_zero.mp h0 with h0 | h0
    ·
      exact Or.inl (eq_of_sub_eq_zero h0)
    ·
      exact Or.inr (Or.inl (eq_of_sub_eq_zero h0))
  ·
    exact Or.inr (Or.inr (eq_of_sub_eq_zero h0))


-- created on 2018-11-24
-- updated on 2026-08-20
