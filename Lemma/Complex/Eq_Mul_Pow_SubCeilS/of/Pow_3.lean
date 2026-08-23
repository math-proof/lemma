import sympy.core.numbers
import Lemma.Complex.ArgPow.eq.SubMul_Arg
import Lemma.Complex.Eq_MulNorm_ExpMulIArg
open Complex


@[main]
private lemma main
  {A B : ℂ}
-- given
  (h : A ^ 3 = B ^ 3) :
-- imply
  let ω : ℂ := (2 * π * I / 3).exp
  let d : ℤ := ⌈3 * arg A / (2 * π) - 1 / 2⌉ - ⌈3 * arg B / (2 * π) - 1 / 2⌉
  A = B * ω ^ d := by
-- proof
  intro ω d
  have harg : arg (A ^ 3) = arg (B ^ 3) := by rw [h]
  have hA3 := ArgPow.eq.SubMul_Arg A 3
  have hB3 := ArgPow.eq.SubMul_Arg B 3
  have hd : (3 : ℝ) * (arg A - arg B) = 2 * π * d := by
    have := harg
    rw [hA3, hB3] at this
    simp [d] at this ⊢
    linarith
  have hθ : arg A - arg B = 2 * π * d / 3 := by
    have hπ : (3 : ℝ) ≠ 0 := by norm_num
    field_simp [hπ]
    linarith
  rw [Eq_MulNorm_ExpMulIArg (z := A), Eq_MulNorm_ExpMulIArg (z := B)]
  have hnorm : ‖A‖ = ‖B‖ := by
    have hp : ‖A‖ ^ 3 = ‖B‖ ^ 3 := by
      simpa [norm_pow] using congrArg norm h
    have hfac :
        ‖A‖ ^ 3 - ‖B‖ ^ 3 =
          (‖A‖ - ‖B‖) * (‖A‖ ^ 2 + ‖A‖ * ‖B‖ + ‖B‖ ^ 2) := by
      ring
    have hdiff : ‖A‖ ^ 3 - ‖B‖ ^ 3 = 0 := by rw [hp]; ring
    by_contra hne
    have hsub : ‖A‖ - ‖B‖ ≠ 0 := sub_ne_zero.mpr hne
    have hsum :
        ‖A‖ ^ 2 + ‖A‖ * ‖B‖ + ‖B‖ ^ 2 = 0 :=
      (mul_eq_zero.mp (hfac.symm.trans hdiff)).resolve_left hsub
    have ha : 0 ≤ ‖A‖ ^ 2 := sq_nonneg _
    have hb : 0 ≤ ‖B‖ ^ 2 := sq_nonneg _
    have hc : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg A) (norm_nonneg B)
    have hA0 : ‖A‖ ^ 2 = 0 := le_antisymm (by linarith) ha
    have hB0 : ‖B‖ ^ 2 = 0 := le_antisymm (by linarith) hb
    exact hne ((sq_eq_zero_iff.mp hA0).trans (sq_eq_zero_iff.mp hB0).symm)
  simp [hnorm, ω]
  have hmul : (I * arg B).exp * (ω ^ d) = (I * arg A).exp := by
    have hz : ω ^ d = exp (↑d * (2 * π * I / 3)) := (exp_int_mul _ d).symm
    rw [hz, ← exp_add]
    congr 1
    have hadd : I * arg B + ↑d * (2 * π * I / 3) = I * arg A := by
      have : (d : ℂ) * (2 * π * I / 3) = I * ↑(2 * π * d / 3) := by
        simp
        ring
      rw [this, ← mul_add, ← ofReal_add]
      congr 2
      linarith [hθ]
    exact hadd
  rw [mul_assoc, hmul]


-- created on 2018-08-28
-- updated on 2026-08-22
