import Lemma.Complex.Eq.of.Re.Im
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Complex Int Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0AddAddPow_3.is.OrEqSAdd.of.EqMul3_Neg.EqAddPowS_3_Neg |
| comm | Complex.OrEqSAdd.is.Eq0AddAddPow_3.of.EqMul3_Neg.EqAddPowS_3_Neg |
| mp | Complex.OrEqSAdd.of.Eq0AddAddPow_3.EqMul3_Neg.EqAddPowS_3_Neg |
| mpr | Complex.Eq0AddAddPow_3.of.OrEqSAdd.EqMul3_Neg.EqAddPowS_3_Neg |
-/
@[main, comm, mp, mpr]
private lemma main
  {x p q A B : ℂ}
-- given
  (h₀ : A ^ 3 + B ^ 3 = -q)
  (h₁ : 3 * A * B = -p) :
-- imply
  x ^ 3 + p * x + q = 0 ↔
    let ω : ℂ := (I * (2 * π / 3)).exp
    x = A + B ∨
      x = A * ω + B * ~ω ∨
      x = A * ~ω + B * ω := by
-- proof
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
  have hωexp : (I * (2 * π / 3)).exp = ω := by
    rw [ExpMulIDivMul2Pi3.eq.Add_MulI]
  have hω3 : ω ^ 3 = 1 := by
    rw [← hωexp, ← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
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
  have hωstar : ω * ~ω = 1 := by
    rw [hstar, (by simp [pow_two, pow_three] : ω * ω ^ 2 = ω ^ 3), hω3]
  have hadd : ω + ~ω = -1 := by
    apply Eq.of.Re.Im
    ·
      simp [add_re, conj_re, hre]
      ring
    ·
      simp [add_im, conj_im, him]
  have hsq' : (~ω) ^ 2 = ω := by
    rw [hstar, ← pow_mul, (by rfl : (2 * 2 : ℕ) = 4)]
    rw [(by rw [(by rfl : (4 : ℕ) = 3 + 1), pow_add, pow_one] : ω ^ 4 = ω ^ 3 * ω), hω3, one_mul]
  have hc3 : (~ω) ^ 3 = 1 := by
    rw [pow_succ, hsq', hωstar]
  have hc4 : (~ω) ^ 4 = ~ω := by
    rw [pow_succ, hc3, one_mul]
  have hc6 : (~ω) ^ 6 = 1 := by
    rw [(by rfl : (6 : ℕ) = 3 + 3), pow_add, hc3, mul_one]
  have hc8 : (~ω) ^ 8 = (~ω) ^ 2 := by
    rw [(by rfl : (8 : ℕ) = 6 + 2), pow_add, hc6, one_mul]
  have cubic_of_sum {A B : ℂ} (hAB : A ^ 3 + B ^ 3 = -q) (hp : 3 * A * B = -p) (hx : x = A + B) :
      x ^ 3 + p * x + q = 0 := by
    subst hx
    calc
      _ = A ^ 3 + B ^ 3 + 3 * A * B * (A + B) + p * (A + B) + q := by
        ring
      _ = (A ^ 3 + B ^ 3 + q) + (3 * A * B + p) * (A + B) := by
        ring
      _ = (-q + q) + (-p + p) * (A + B) := by
        rw [hp, hAB]
      _ = 0 := by
        ring
  constructor
  ·
    intro h
    suffices hOr : x = A + B ∨ x = A * ω + B * ~ω ∨ x = A * ~ω + B * ω by
      simpa [hωexp] using hOr
    have hprod : (x - (A + B)) * (x - (A * ω + B * ~ω)) * (x - (A * ~ω + B * ω)) = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
      rw [← hstar.symm, ← hsq']
      ring_nf
      rw [hc8, hc6, hc4, hsq']
      simp only [mul_one]
      rw [← EqSub.of.Eq_Add (y := (-1 : ℂ)) (d := ~ω) (x := ω) (by rwa [add_comm, eq_comm])]
      ring
    obtain h0 | h0 := OrEqS_0.of.Mul.eq.Zero (by
      have : x ^ 3 + p * x + q = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
        rw [h₁, h₀]
        ring
      rw [hprod, ← this, h])
    ·
      obtain h0 | h0 := OrEqS_0.of.Mul.eq.Zero h0
      ·
        apply Or.inl
        apply Eq.of.Sub.eq.Zero h0
      ·
        apply Or.inr
        apply Or.inl
        apply Eq.of.Sub.eq.Zero h0
    ·
      apply Or.inr
      apply Or.inr
      apply Eq.of.Sub.eq.Zero h0
  ·
    intro h
    obtain hx | hx | hx := h
    ·
      apply cubic_of_sum h₀ h₁ hx
    ·
      rw [hωexp] at hx
      apply cubic_of_sum (A := A * ω) (B := B * ~ω)
      ·
        rw [mul_pow, mul_pow, hω3, hc3, mul_one, mul_one, h₀]
      ·
        calc
          _ = 3 * A * B * (ω * ~ω) := by
            ring
          _ = 3 * A * B := by
            rw [hωstar, mul_one]
          _ = -p := by
            rw [h₁]
      ·
        apply hx
    ·
      rw [hωexp] at hx
      apply cubic_of_sum (A := A * ~ω) (B := B * ω)
      ·
        rw [mul_pow, mul_pow, hc3, hω3, mul_one, mul_one, h₀]
      ·
        calc
          _ = 3 * A * B * (~ω * ω) := by
            ring
          _ = 3 * A * B := by
            rw [mul_comm (~ω), hωstar, mul_one]
          _ = -p := by
            rw [h₁]
      ·
        apply hx


-- created on 2026-08-28
-- updated on 2026-08-29
