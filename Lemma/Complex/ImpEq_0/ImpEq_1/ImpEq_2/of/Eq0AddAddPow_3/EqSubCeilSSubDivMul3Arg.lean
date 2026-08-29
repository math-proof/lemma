import Lemma.Complex.Eq_Mul_Pow_SubCeilS.of.Pow_3
import Lemma.Complex.EqSquareSqrt
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Complex Int Nat


/--
Cardano's formula for solving cubic equations
-/
@[main]
private lemma main
  {x p q : ℂ}
  {d : ℤ}
-- given
  (h : x ^ 3 + p * x + q = 0)
  (hd : ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
    (
      let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
      let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    ) = d) :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (d % 3 = 0 →
      x = A + B ∨
        x = A * ω + B * ~ω ∨
        x = A * ~ω + B * ω) ∧
    (d % 3 = 1 →
      x = A * ω + B ∨
        x = A * ~ω + B * ~ω ∨
        x = A + B * ω) ∧
    (d % 3 = 2 →
      x = A * ~ω + B ∨
        x = A + B * ~ω ∨
        x = A * ω + B * ω) := by
-- proof
  intro δ A B ω
  extract_lets at hd
  have hA3 : A ^ 3 = √δ / 2 - q / 2 := by
    simp [A]
  have hB3 : B ^ 3 = -√δ / 2 - q / 2 := by
    simp [B]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hωexp : (2 * π * I / 3).exp = ω := by
    have : (2 * π * I / 3 : ℂ) = ↑(2 * π / 3 : ℝ) * I := by
      simp [div_eq_mul_inv]
      ring
    rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin, (by ring : (2 * π / 3 : ℝ) = π - π / 3), Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp [ω]
    ring_nf
    rfl
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
  have hωne : ω ≠ 0 := by
    rw [← hωexp]
    apply exp_ne_zero
  have hωstar : ω * ~ω = 1 := by
    rw [hstar, (by simp [pow_two, pow_three] : ω * ω ^ 2 = ω ^ 3), hω3]
  have hABd : A * B * ω ^ d = -p / 3 := by
    have hmul : (√δ / 2 - q / 2) * (-√δ / 2 - q / 2) = -(δ - q ^ 2) / 4 := calc
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
    have : A * B = (-p / 3) * ω ^ (-d) := by
      apply h.trans
      rw [(by linarith [hd] : ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ = -d)]
    rw [this, mul_assoc, ← zpow_add₀ hωne]
    simp [neg_add_cancel]
  have hωdmod (n : ℤ) : ω ^ n = ω ^ (n % 3) := by
    conv_lhs => rw [(by omega : n = n % 3 + 3 * (n / 3))]
    rw [zpow_add₀ hωne, (by rw [zpow_mul, zpow_ofNat, hω3, one_zpow] : ω ^ (3 * (n / 3) : ℤ) = 1), mul_one]
  have cardano_of_identities {A B : ℂ} (hAB : A ^ 3 + B ^ 3 = -q) (hp : 3 * A * B = -p) : x = A + B ∨ x = A * ω + B * ~ω ∨ x = A * ~ω + B * ω := by
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
    have hprod : (x - (A + B)) * (x - (A * ω + B * ~ω)) * (x - (A * ~ω + B * ω)) = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
      rw [← hstar.symm, ← hsq']
      ring_nf
      rw [hc8, hc6, hc4, hsq']
      simp only [mul_one]
      rw [← EqSub.of.Eq_Add (y := (-1 : ℂ)) (d := ~ω) (x := ω) (by rwa [add_comm, eq_comm])]
      ring
    obtain h0 | h0 := OrEqS_0.of.Mul.eq.Zero (by
      have : x ^ 3 + p * x + q = x ^ 3 - 3 * A * B * x - (A ^ 3 + B ^ 3) := by
        rw [hp, hAB]
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
  refine ⟨?_, ?_, ?_⟩
  ·
    intro h0
    apply cardano_of_identities hA3B3
    convert (by
      rw [(by simpa [(by rw [hωdmod, h0, zpow_zero] : ω ^ d = 1), mul_one] using hABd : A * B = -p / 3)]
      ring : 3 * (A * B) = -p) using 1
    ring
  ·
    intro h1
    let A' : ℂ := A * ω
    obtain hx | hx | hx := cardano_of_identities (A := A') (B := B)
      (by
        simp only [A']
        rw [mul_pow, hω3, mul_one, hA3B3])
      (by
        simp only [A']
        calc
          _ = 3 * (A * B * ω) := by
            ring
          _ = 3 * (-p / 3) := by
            rw [(by simpa [(by rw [hωdmod, h1, zpow_one] : ω ^ d = ω)] using hABd : A * B * ω = -p / 3)]
          _ = -p := by
            ring)
    ·
      apply Or.inl
      simpa [A'] using hx
    ·
      apply Or.inr
      apply Or.inl
      change x = A' * ω + B * ~ω at hx
      apply Eq.trans hx
      congr 1
      dsimp [A']
      calc
        _ = A * (ω * ω) := by
          rw [mul_assoc]
        _ = A * ω ^ 2 := by
          rw [← pow_two]
        _ = A * ~ω := by
          rw [hstar]
    ·
      apply Or.inr
      apply Or.inr
      change x = A' * ~ω + B * ω at hx
      apply Eq.trans hx
      congr 1
      dsimp [A']
      rw [mul_assoc, hωstar, mul_one]
  ·
    intro h2
    let A' : ℂ := A * ~ω
    obtain hx | hx | hx := cardano_of_identities (A := A') (B := B)
      (by
        simp only [A', hstar]
        rw [mul_pow, (by rw [← pow_mul, (by rfl : (2 * 3 : ℕ) = 6), (by rw [← pow_mul] : ω ^ 6 = (ω ^ 3) ^ 2), hω3, one_pow] : (ω ^ 2) ^ 3 = 1), mul_one, hA3B3])
      (by
        simp only [A', hstar]
        calc
          _ = 3 * (A * B * ω ^ 2) := by
            ring
          _ = 3 * (-p / 3) := by
            rw [(by simpa [(by rw [hωdmod d, h2, zpow_ofNat] : ω ^ d = ω ^ 2)] using hABd : A * B * ω ^ 2 = -p / 3)]
          _ = -p := by
            ring)
    ·
      apply Or.inl
      simpa [A'] using hx
    ·
      apply Or.inr
      apply Or.inl
      change x = A' * ω + B * ~ω at hx
      apply Eq.trans hx
      congr 1
      dsimp [A']
      rw [mul_assoc, mul_comm (~ω) ω, hωstar, mul_one]
    ·
      apply Or.inr
      apply Or.inr
      change x = A' * ~ω + B * ω at hx
      apply Eq.trans hx
      congr 1
      dsimp [A']
      rw [hstar, mul_assoc, ← pow_add, (by rfl : (2 + 2 : ℕ) = 4)]
      rw [(by rw [(by rfl : (4 : ℕ) = 3 + 1), pow_add, pow_one, hω3, one_mul] : ω ^ 4 = ω)]


-- created on 2018-11-15
-- updated on 2026-08-29
