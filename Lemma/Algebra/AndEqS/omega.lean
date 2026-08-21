import sympy.functions.elementary.complexes
import sympy.core.numbers
import sympy.Basic


@[main]
private lemma main :
-- imply
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  ω = ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I ∧
    (starRingEnd ℂ) ω = ↑(-(1 / 2 : ℝ)) + ↑(-(√3 / 2 : ℝ)) * I ∧
    ω + (starRingEnd ℂ) ω = -1 ∧
    ω * (starRingEnd ℂ) ω = 1 ∧
    ω ^ 2 = (starRingEnd ℂ) ω ∧
    ((starRingEnd ℂ) ω) ^ 2 = ω ∧
    ω ^ 3 = 1 := by
-- proof
  intro ω
  have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hconj : (starRingEnd ℂ) ω = ↑(-(1 / 2 : ℝ)) + ↑(-(√3 / 2 : ℝ)) * I := by
    apply Complex.ext
    ·
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, hre]
      ring
    ·
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_im, him]
      ring
  refine ⟨rfl, hconj, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply Complex.ext
    ·
      simp [Complex.add_re, Complex.conj_re, hre]
      ring
    ·
      simp [Complex.add_im, Complex.conj_im, him]
  ·
    rw [Complex.mul_conj, Complex.normSq_apply, hre, him]
    ring_nf
    rw [h3]
    norm_num
  ·
    apply Complex.ext
    ·
      simp [pow_two, Complex.mul_re, Complex.conj_re, hre, him]
      ring_nf
      rw [h3]
      ring
    ·
      simp [pow_two, Complex.mul_im, Complex.conj_im, hre, him]
      ring
  ·
    apply Complex.ext
    ·
      simp [pow_two, Complex.mul_re, Complex.conj_re, hre, him]
      ring_nf
      rw [h3]
      ring
    ·
      simp [pow_two, Complex.mul_im, Complex.conj_im, hre, him]
      ring
  ·
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


-- created on 2018-08-18
-- updated on 2026-08-20
