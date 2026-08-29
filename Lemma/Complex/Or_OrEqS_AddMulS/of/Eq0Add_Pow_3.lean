import Lemma.Complex.Eq0Add_Pow_3.is.Or_OrEqS_AddMulS.of.EqNeg_MulMul3.EqNeg_AddPowS_3
import Lemma.Complex.Eq.of.Re.Im
import Lemma.Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3
import Lemma.Complex.EqSquareSqrt
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
open Complex


/--
Cardano's formula for solving cubic equations
-/
@[main]
private lemma Cardano
  {x p q : ℂ}
-- given
  (h : q + p * x + x ^ 3 = 0) :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := (I * (2 * π / 3)).exp
  let k : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  x = A * ω ^ k + B ∨
    x = A * ω ^ (k - 1) + B * ω ∨
    x = A * ω ^ (k + 1) + B * ~ω := by
-- proof
  intro δ A B ω k
  have hA3 : A ^ 3 = (-q + √δ) / 2 := by
    simp [A]
  have hB3 : B ^ 3 = (-q - √δ) / 2 := by
    simp [B]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hωexp : (I * (2 * π / 3)).exp = ω := rfl
  have hωrect : ω = ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ) :=
    ExpMulIDivMul2Pi3.eq.Add_MulI
  have hω3 : ω ^ 3 = 1 := by
    rw [← hωexp, ← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
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
  have hωne : ω ≠ 0 := by
    rw [← hωexp]
    apply exp_ne_zero
  have hωstar : ω * ~ω = 1 := by
    rw [hstar, (by simp [pow_two, pow_three] : ω * ω ^ 2 = ω ^ 3), hω3]
  have hABk : A * B * ω ^ k = -p / 3 := by
    have hmul : ((-q + √δ) / 2) * ((-q - √δ) / 2) = -(δ - q ^ 2) / 4 := calc
      _ = -((√δ / 2) * (√δ / 2) - (q / 2) * (q / 2)) := by
        ring
      _ = -(√δ * √δ / 4 - q ^ 2 / 4) := by
        ring
      _ = -(δ / 4 - q ^ 2 / 4) := by
        rw [(by simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ) : √δ * √δ = δ)]
      _ = -(δ - q ^ 2) / 4 := by
        ring
    have h := Eq_Mul_Pow_SubCeilS.of.Pow_3 (A := A * B) (B := -p / 3) (by
      rw [mul_pow, hA3, hB3, hmul, (by simp [δ] : δ - q ^ 2 = 4 * p ^ 3 / 27)]
      ring)
    simp [hωexp, -one_div] at h
    have : A * B = (-p / 3) * ω ^ (-k) := by
      apply h.trans
      simp [k]
    rw [this, mul_assoc, ← zpow_add₀ hωne]
    simp [neg_add_cancel]
  let A' : ℂ := A * ω ^ k
  obtain hx | hx | hx :=
    Or_OrEqS_AddMulS.of.Eq0Add_Pow_3.EqNeg_MulMul3.EqNeg_AddPowS_3 (A := A') (B := B)
      (by
        simp only [A']
        rw [mul_pow,
          (by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω3, one_zpow] :
            (ω ^ k) ^ (3 : ℕ) = 1),
          mul_one, hA3B3])
      (by
        simp only [A']
        calc
          _ = 3 * (A * B * ω ^ k) := by
            ring
          _ = 3 * (-p / 3) := by
            rw [hABk]
          _ = -p := by
            ring)
      h
  ·
    apply Or.inl
    simpa [A'] using hx
  ·
    apply Or.inr
    apply Or.inr
    rw [hωexp] at hx
    apply Eq.trans hx
    congr 1
    dsimp [A']
    rw [mul_assoc, ← zpow_add_one₀ hωne]
  ·
    apply Or.inr
    apply Or.inl
    rw [hωexp] at hx
    apply Eq.trans hx
    congr 1
    dsimp [A']
    rw [mul_assoc,
      (by
        rw [← inv_eq_of_mul_eq_one_right hωstar, ← zpow_neg_one, ← zpow_add₀ hωne, sub_eq_add_neg] :
        ω ^ k * ~ω = ω ^ (k - 1))]


-- created on 2018-11-15
-- updated on 2026-08-29
