import Lemma.Complex.ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
import sympy.polys.polyroots
open Complex


@[main]
private lemma main
  {A B : ℂ}
  {d : ℤ}
-- given
  (h : ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = d) :
-- imply
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
  ∛A * ∛B = ∛(A * B) * ω ^ d := by
-- proof
  intro ω
  simp only [Root.cubic]
  have hexp : (3 : ℂ)⁻¹ ≠ 0 := by norm_num
  by_cases hA : A = 0
  ·
    simp [hA]
  ·
    by_cases hB : B = 0
    ·
      simp [hB]
    ·
      have hAB : A * B ≠ 0 := mul_ne_zero hA hB
      rw [cpow_def_of_ne_zero hA, cpow_def_of_ne_zero hB, cpow_def_of_ne_zero hAB]
      have harg : arg (A * B) = arg A + arg B - 2 * π * d := by
        rw [ArgMul.eq.SubAddArgSMul_Ceil.of.Ne_0.Ne_0 hA hB, h]
      have hlog : log (A * B) = log A + log B - 2 * π * I * d := by
        simp only [log, harg, norm_mul]
        rw [Real.log_mul (ne_of_gt (norm_pos_iff.mpr hA)) (ne_of_gt (norm_pos_iff.mpr hB))]
        simp [ofReal_add, ofReal_sub]
        ring
      have hωexp : (I * (2 * π / 3)).exp = ω := by
        simp only [ω, Root.sqrt]
        apply ExpMulIDivMul2Pi3.eq.Add_MulI
      rw [← exp_add]
      have hadd :
          log A * (3 : ℂ)⁻¹ + log B * (3 : ℂ)⁻¹ =
            (log (A * B) + 2 * π * I * d) * (3 : ℂ)⁻¹ := by
        rw [hlog]
        ring
      rw [hadd, add_mul, exp_add]
      have hdiv : (2 * π * I * d) * (3 : ℂ)⁻¹ = 2 * π * I * d / 3 := by
        field_simp
      rw [hdiv]
      rw [show (2 * π * I * d / 3 : ℂ) = d * (I * (2 * π / 3)) by ring, exp_int_mul, hωexp]


-- created on 2018-10-26
-- updated on 2026-08-29
