import Lemma.Complex.Eq.of.Re.Im
import Lemma.Complex.Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqModSubCeilSSubDivMul3Arg
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : x =
    let p : ℂ := b - a ^ 2 / 3
    let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
    let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
    let k : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    A * ω ^ k + B - a / 3) :
-- imply
  c + b * x + a * x ^ 2 + x ^ 3 = 0 := by
-- proof
  extract_lets p q ω δ A B k at h
  let z : ℂ := A * ω ^ k + B
  have hωrect : ω = ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ) :=
    ExpMulIDivMul2Pi3.eq.Add_MulI
  have hre : ω.re = -(1 / 2) := by
    simp only [hωrect, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [hωrect, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have h3r : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hstar : ~ω = ω ^ 2 := by
    apply Eq.of.Re.Im
    ·
      simp [pow_two, mul_re, conj_re, hre, him]
      ring_nf
      rw [h3r]
      ring
    ·
      simp [pow_two, mul_im, conj_im, hre, him]
      ring
  have hωne : ω ≠ 0 := exp_ne_zero _
  have hω3 : ω ^ 3 = 1 := by
    rw [← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have hωkmod (n : ℤ) : ω ^ n = ω ^ (n % 3) := by
    conv_lhs => rw [(by omega : n = n % 3 + 3 * (n / 3))]
    rw [zpow_add₀ hωne, (by rw [zpow_mul, zpow_ofNat, hω3, one_zpow] : ω ^ (3 * (n / 3) : ℤ) = 1), mul_one]
  have hz : z ^ 3 + p * z + q = 0 := by
    let m : ℤ := k % 3
    have hite :
        A * ω ^ k + B =
          if m = 0 then A + B else if m = 1 then A * ω + B else A * ~ω + B := by
      simp only [m]
      rw [hωkmod]
      if h0 : k % 3 = 0 then
        simp [h0]
      else if h1 : k % 3 = 1 then
        simp [h1]
      else
        have h2 : k % 3 = 2 := by omega
        simp [h2, zpow_ofNat, hstar]
    apply Eq0AddAddPow_3.of.Eq_Ite_Add_Pow_Inv3.EqModSubCeilSSubDivMul3Arg (p := p) (q := q) (x := z) (k := m)
    ·
      simp [k, m, A, B, δ]
    ·
      extract_lets
      simpa [z] using hite
  have hx : x = z - a / 3 := by
    simpa [z] using h
  rw [hx]
  simp only [p, q] at hz ⊢
  convert hz using 1
  ring


-- created on 2018-11-20
-- updated on 2026-08-29
