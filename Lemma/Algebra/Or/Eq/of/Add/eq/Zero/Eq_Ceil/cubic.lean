import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Algebra.And.Imp.Or.Eq.of.Add.eq.Zero.cubic.depressed
import Lemma.Algebra.Eq.of.Eq_Pow.cubic_root.omega
import Lemma.Bool.Eq.CubeCubic
import Lemma.Complex.EqSquareSqrt
open Algebra Bool Complex


@[main]
private lemma main
  {x p q : ℂ}
-- given
  (h : x ^ 3 + p * x + q = 0) :
-- imply
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (d = 0 →
      x = A + B ∨
        x = A * ω + B * (starRingEnd ℂ) ω ∨
        x = A * (starRingEnd ℂ) ω + B * ω) ∧
    (d % 3 = 1 →
      x = A * ω + B ∨
        x = A * (starRingEnd ℂ) ω + B * (starRingEnd ℂ) ω ∨
        x = A + B * ω) ∧
    (d % 3 = 2 →
      x = A * (starRingEnd ℂ) ω + B ∨
        x = A + B * (starRingEnd ℂ) ω ∨
        x = A * ω + B * ω) := by
-- proof
  intro δ A B d ω
  have hA3 : A ^ 3 = √δ / 2 - q / 2 := by
    simp [A]
  have hB3 : B ^ 3 = -√δ / 2 - q / 2 := by
    simp [B]
  have hA3B3 : A ^ 3 + B ^ 3 = -q := by
    rw [hA3, hB3]
    ring
  have hsq : √δ * √δ = δ := by
    simpa [pow_two] using (EqSquareSqrt : (√δ)² = δ)
  have hprod3 : (A * B) ^ 3 = (-p / 3) ^ 3 := by
    rw [mul_pow, hA3, hB3]
    have hmul : (√δ / 2 - q / 2) * (-√δ / 2 - q / 2) = -(δ - q ^ 2) / 4 := by
      calc
        (√δ / 2 - q / 2) * (-√δ / 2 - q / 2) =
            -((√δ / 2) * (√δ / 2) - (q / 2) * (q / 2)) := by ring
        _ = -(√δ * √δ / 4 - q ^ 2 / 4) := by ring
        _ = -(δ / 4 - q ^ 2 / 4) := by rw [hsq]
        _ = -(δ - q ^ 2) / 4 := by ring
    have hδq : δ - q ^ 2 = 4 * p ^ 3 / 27 := by
      simp [δ]
    rw [hmul, hδq]
    ring
  have hrot := Eq.of.Eq_Pow.cubic_root.omega (A := A * B) (B := -p / 3) hprod3
  have hωexp : (2 * π * I / 3).exp = ω := by
    have hmul : (2 * π * I / 3 : ℂ) = ↑(2 * π / 3 : ℝ) * I := by
      simp [div_eq_mul_inv]
      ring
    rw [hmul, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    have hθ : (2 * π / 3 : ℝ) = π - π / 3 := by ring
    rw [hθ, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp [ω]
    ring_nf
    rfl
  have hω3 : ω ^ 3 = 1 := by
    rw [← hωexp, ← exp_nat_mul]
    convert exp_two_pi_mul_I using 2
    ring
  have h3r : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have hstar : (starRingEnd ℂ) ω = ω ^ 2 := by
    apply Complex.ext
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
    exact exp_ne_zero _
  have hωstar : ω * (starRingEnd ℂ) ω = 1 := by
    rw [hstar]
    have : ω * ω ^ 2 = ω ^ 3 := by
      simp [pow_two, pow_three]
    rw [this, hω3]
  have hAB : A * B = (-p / 3) * ω ^ (-d) := by
    have h := hrot
    simp [hωexp] at h
    convert h using 1
    simp [d]
  have hABd : A * B * ω ^ d = -p / 3 := by
    rw [hAB, mul_assoc, ← zpow_add₀ hωne]
    simp [neg_add_cancel, zpow_zero]
  have hωdmod (n : ℤ) : ω ^ n = ω ^ (n % 3) := by
    have hsplit : n % 3 + 3 * (n / 3) = n := by omega
    conv_lhs => rw [← hsplit]
    rw [zpow_add₀ hωne]
    have : ω ^ (3 * (n / 3) : ℤ) = 1 := by
      rw [zpow_mul]
      have h3z : ω ^ (3 : ℤ) = 1 := by
        rw [zpow_ofNat]
        exact hω3
      rw [h3z, one_zpow]
    rw [this, mul_one]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hd0
    have hpAB : 3 * A * B = -p := by
      have hAB0 : A * B = -p / 3 := by
        simpa [hd0, zpow_zero, mul_one] using hABd
      have : 3 * (A * B) = -p := by
        rw [hAB0]
        ring
      convert this using 1
      ring
    exact And.Imp.Or.Eq.of.Add.eq.Zero.cubic.depressed h hA3B3 hpAB
  ·
    intro hd1
    let A' : ℂ := A * ω
    have hA'3 : A' ^ 3 = A ^ 3 := by
      simp only [A']
      rw [mul_pow, hω3, mul_one]
    have hA'B3 : A' ^ 3 + B ^ 3 = -q := by
      rw [hA'3, hA3B3]
    have hpA' : 3 * A' * B = -p := by
      have hωd : ω ^ d = ω := by
        rw [hωdmod, hd1, zpow_one]
      have hABω : A * B * ω = -p / 3 := by
        simpa [hωd] using hABd
      simp only [A']
      calc
        3 * (A * ω) * B = 3 * (A * B * ω) := by ring
        _ = 3 * (-p / 3) := by rw [hABω]
        _ = -p := by ring
    have hx := And.Imp.Or.Eq.of.Add.eq.Zero.cubic.depressed h hA'B3 hpA'
    rcases hx with hx | hx | hx
    ·
      exact Or.inl (by simpa [A'] using hx)
    ·
      refine Or.inr (Or.inl ?_)
      change x = A' * ω + B * (starRingEnd ℂ) ω at hx
      have heq : A' * ω = A * (starRingEnd ℂ) ω := by
        dsimp [A']
        calc
          A * ω * ω = A * (ω * ω) := by rw [mul_assoc]
          _ = A * ω ^ 2 := by rw [← pow_two]
          _ = A * (starRingEnd ℂ) ω := by rw [hstar]
      rw [heq] at hx
      exact hx
    ·
      refine Or.inr (Or.inr ?_)
      change x = A' * (starRingEnd ℂ) ω + B * ω at hx
      have heq : A' * (starRingEnd ℂ) ω = A := by
        dsimp [A']
        rw [mul_assoc, hωstar, mul_one]
      rw [heq] at hx
      exact hx
  ·
    intro hd2
    let A' : ℂ := A * (starRingEnd ℂ) ω
    have hA'3 : A' ^ 3 = A ^ 3 := by
      simp only [A', hstar]
      rw [mul_pow]
      have : (ω ^ 2) ^ 3 = 1 := by
        rw [← pow_mul, show (2 * 3 : ℕ) = 6 from rfl]
        have : ω ^ 6 = (ω ^ 3) ^ 2 := by rw [← pow_mul]
        rw [this, hω3, one_pow]
      rw [this, mul_one]
    have hA'B3 : A' ^ 3 + B ^ 3 = -q := by
      rw [hA'3, hA3B3]
    have hpA' : 3 * A' * B = -p := by
      have hωd : ω ^ d = ω ^ 2 := by
        rw [hωdmod d, hd2, zpow_ofNat]
      have hABω : A * B * ω ^ 2 = -p / 3 := by
        simpa [hωd] using hABd
      simp only [A', hstar]
      calc
        3 * (A * ω ^ 2) * B = 3 * (A * B * ω ^ 2) := by ring
        _ = 3 * (-p / 3) := by rw [hABω]
        _ = -p := by ring
    have hx := And.Imp.Or.Eq.of.Add.eq.Zero.cubic.depressed h hA'B3 hpA'
    rcases hx with hx | hx | hx
    ·
      exact Or.inl (by simpa [A'] using hx)
    ·
      refine Or.inr (Or.inl ?_)
      change x = A' * ω + B * (starRingEnd ℂ) ω at hx
      have heq : A' * ω = A := by
        dsimp [A']
        have : (starRingEnd ℂ) ω * ω = 1 := by
          rw [mul_comm, hωstar]
        rw [mul_assoc, this, mul_one]
      rw [heq] at hx
      exact hx
    ·
      refine Or.inr (Or.inr ?_)
      change x = A' * (starRingEnd ℂ) ω + B * ω at hx
      have heq : A' * (starRingEnd ℂ) ω = A * ω := by
        dsimp [A']
        rw [hstar]
        have hω4 : ω ^ 4 = ω := by
          have : ω ^ 4 = ω ^ 3 * ω := by
            rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, pow_one]
          rw [this, hω3, one_mul]
        rw [mul_assoc, ← pow_add]
        have : (2 + 2 : ℕ) = 4 := by norm_num
        rw [this, hω4]
      rw [heq] at hx
      exact hx


-- created on 2018-11-15
-- updated on 2026-08-20
