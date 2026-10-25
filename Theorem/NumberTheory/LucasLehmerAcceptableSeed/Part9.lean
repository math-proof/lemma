/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Def.NumberTheory.LucasLehmerAcceptableSeed.Part4
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_delta_fst (s₁ : ℤ) (q : ℕ) :
    (lucasLehmerSeed_delta s₁ q).1 = 0 := rfl

@[simp] theorem lucasLehmerSeed_delta_snd (s₁ : ℤ) (q : ℕ) :
    (lucasLehmerSeed_delta s₁ q).2 = 1 := rfl

@[simp] theorem lucasLehmerSeed_delta_sq (s₁ : ℤ) (q : ℕ) :
    lucasLehmerSeed_delta s₁ q ^ 2 =
      (lucasLehmerSeed_D s₁ q : lucasLehmerSeed_X s₁ q) := by
  apply lucasLehmerSeed_X_ext
  · simp only [pow_two, lucasLehmerSeed_mul_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd, lucasLehmerSeed_coeZMod_fst]
    ring
  · simp only [pow_two, lucasLehmerSeed_mul_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd, lucasLehmerSeed_coeZMod_snd]
    ring

theorem lucasLehmerSeed_alpha_eq (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_alpha s₁ q =
      ((((s₁ : ZMod q) / (2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) +
        (1 / 2 : ZMod q) * lucasLehmerSeed_delta s₁ q := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_alpha_fst, lucasLehmerSeed_add_fst,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_mul_fst,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring
  · simp only [lucasLehmerSeed_alpha_snd, lucasLehmerSeed_add_snd,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_mul_snd,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring

theorem lucasLehmerSeed_beta_eq (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_beta s₁ q =
      ((((s₁ : ZMod q) / (2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) +
        (((-(1 / 2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) *
          lucasLehmerSeed_delta s₁ q := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_beta_fst, lucasLehmerSeed_add_fst,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_mul_fst,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring
  · simp only [lucasLehmerSeed_beta_snd, lucasLehmerSeed_add_snd,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_mul_snd,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring

theorem lucasLehmerSeed_alpha_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
    lucasLehmerSeed_alpha s₁ q ^ q = lucasLehmerSeed_beta s₁ q := by
  rw [lucasLehmerSeed_alpha_eq, add_pow_expChar, mul_pow,
    lucasLehmerSeed_coeZMod_pow_q s₁ q ((s₁ : ZMod q) / 2),
    lucasLehmerSeed_coeZMod_pow_q s₁ q (1 / 2),
    lucasLehmerSeed_delta_pow_q s₁ q hq_odd hD, lucasLehmerSeed_beta_eq]
  rw [map_neg]
  ring

theorem lucasLehmerSeed_one_add_alpha_pow_q_succ
    (s₁ : ℤ) (q : ℕ) [Fact q.Prime] (hq_odd : Odd q)
    (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
    (1 + lucasLehmerSeed_alpha s₁ q) ^ (q + 1) =
      (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
  rw [pow_succ, add_pow_expChar, one_pow,
    lucasLehmerSeed_alpha_pow_q s₁ q hq_odd hD]
  rw [show (1 + lucasLehmerSeed_beta s₁ q) *
      (1 + lucasLehmerSeed_alpha s₁ q) =
      2 + (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q) by
        calc
          (1 + lucasLehmerSeed_beta s₁ q) *
              (1 + lucasLehmerSeed_alpha s₁ q) =
              1 + lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q +
                lucasLehmerSeed_beta s₁ q * lucasLehmerSeed_alpha s₁ q := by ring
          _ = 2 + (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q) := by
            rw [lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd]
            ring]
  rw [lucasLehmerSeed_alpha_add_beta s₁ q hq_odd]
  ring

theorem lucasLehmerSeed_one_add_alpha_sq (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    (1 + lucasLehmerSeed_alpha s₁ q) ^ 2 =
      lucasLehmerSeed_alpha s₁ q *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
  calc
    (1 + lucasLehmerSeed_alpha s₁ q) ^ 2 =
        lucasLehmerSeed_alpha s₁ q ^ 2 + 2 * lucasLehmerSeed_alpha s₁ q + 1 := by
      ring
    _ = lucasLehmerSeed_alpha s₁ q ^ 2 + 2 * lucasLehmerSeed_alpha s₁ q +
        lucasLehmerSeed_alpha s₁ q * lucasLehmerSeed_beta s₁ q := by
      rw [lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd]
    _ = lucasLehmerSeed_alpha s₁ q *
        (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q + 2) := by ring
    _ = lucasLehmerSeed_alpha s₁ q *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
      rw [lucasLehmerSeed_alpha_add_beta s₁ q hq_odd]

theorem lucasLehmerSeed_alpha_pow_half (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1)
    (hplus : legendreSym q (s₁ + 2) = -1) :
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) = -1 := by
  have htwo : 2 * ((q + 1) / 2) = q + 1 := Nat.two_mul_div_two_of_even hq_odd.add_one
  have htrace :
      lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
          (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    calc
      lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
          (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
          (lucasLehmerSeed_alpha s₁ q *
            (s₁ + 2 : lucasLehmerSeed_X s₁ q)) ^ ((q + 1) / 2) :=
        (mul_pow _ _ _).symm
      _ = ((1 + lucasLehmerSeed_alpha s₁ q) ^ 2) ^ ((q + 1) / 2) := by
        rw [lucasLehmerSeed_one_add_alpha_sq s₁ q hq_odd]
      _ = (1 + lucasLehmerSeed_alpha s₁ q) ^ (q + 1) := by
        rw [← pow_mul, htwo]
      _ = (s₁ + 2 : lucasLehmerSeed_X s₁ q) :=
        lucasLehmerSeed_one_add_alpha_pow_q_succ s₁ q hq_odd hD
  have hplus_pow : ((s₁ + 2 : ℤ) : ZMod q) ^ (q / 2) = -1 := by
    have h := legendreSym.eq_pow q (s₁ + 2)
    rw [hplus] at h
    simpa using h.symm
  obtain ⟨k, hk⟩ := hq_odd
  have hhalf : (q + 1) / 2 = q / 2 + 1 := by omega
  have hcast :
      (((s₁ + 2 : ℤ) : ZMod q) : lucasLehmerSeed_X s₁ q) =
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [map_intCast]
    push_cast
    rfl
  have hbase_pow :
      (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
        -(s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [← hcast, hhalf, pow_succ, ← map_pow, hplus_pow, map_neg]
    simp
  rw [hbase_pow] at htrace
  have hbase_ne : ((s₁ + 2 : ℤ) : ZMod q) ≠ 0 := by
    intro hz
    have := (legendreSym.eq_zero_iff q (s₁ + 2)).2 hz
    rw [hplus] at this
    norm_num at this
  have hunit_z : IsUnit (((s₁ + 2 : ℤ) : ZMod q)) := isUnit_iff_ne_zero.mpr hbase_ne
  have hunit : IsUnit (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [← hcast]
    exact hunit_z.map (ZMod.castHom dvd_rfl (lucasLehmerSeed_X s₁ q))
  have hcancel := hunit.mul_right_cancel <| show
    (lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) * -1) *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) =
      1 * (s₁ + 2 : lucasLehmerSeed_X s₁ q) by
        calc
          _ = lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
              -(s₁ + 2 : lucasLehmerSeed_X s₁ q) := by ring
          _ = (s₁ + 2 : lucasLehmerSeed_X s₁ q) := htrace
          _ = _ := by ring
  calc
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) =
        -(lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) * -1) := by ring
    _ = -1 := by rw [hcancel]

theorem lucasLehmerSeed_trace_zero (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1)
    (hplus : legendreSym q (s₁ + 2) = -1) (hq4 : 4 ∣ q + 1) :
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 4) +
      lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) = 0 := by
  have hmul : lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
      lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) =
      -lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) := by
    rw [lucasLehmerSeed_alpha_pow_half s₁ q hq_odd hD hplus]
    ring
  have hsplit : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by
    obtain ⟨k, hk⟩ := hq4
    omega
  rw [hsplit, pow_add, mul_assoc, ← mul_pow,
    lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd, one_pow, mul_one] at hmul
  rw [hmul]
  ring

theorem lucasLehmerSeed_necessity (n : ℕ) (hn_odd : Odd n) (hn_ge : 3 ≤ n)
    (s₁ : ℤ)
    (hjac : jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
      jacobiSym (s₁ - 2) (mersenne n) = 1)
    (hprime : (mersenne n).Prime) :
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁ := by
  set p' := n - 2 with hp'
  clear_value p'
  obtain rfl : n = p' + 2 := by omega
  have : Fact (mersenne (p' + 2)).Prime := ⟨hprime⟩
  have hq_odd : Odd (mersenne (p' + 2)) := mersenne_odd.2 (by omega)
  have hplus := lucasLehmerSeed_legendre_add_two s₁ (mersenne (p' + 2)) hjac.1
  have hminus := lucasLehmerSeed_legendre_sub_two s₁ (mersenne (p' + 2)) hjac.2
  have hD := lucasLehmerSeed_legendre_D s₁ (mersenne (p' + 2)) hplus hminus
  have htrace := lucasLehmerSeed_trace_zero s₁ (mersenne (p' + 2)) hq_odd hD hplus
    (by simp [succ_mersenne, pow_add])
  rw [succ_mersenne, pow_add, show 2 ^ 2 = 4 by norm_num,
    mul_div_cancel_right₀ _ (by norm_num)] at htrace
  have hclosed := lucasLehmerSeed_closedForm s₁ (mersenne (p' + 2)) hq_odd p'
  have hzero :
      ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁ : ℤ) :
        ZMod (mersenne (p' + 2))) = 0 := by
    rw [← lucasLehmerSeed_intCast_fst
      (s₁ := s₁) (q := mersenne (p' + 2))]
    rw [hclosed, htrace]
    simp
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hzero

/--
A seed `s₁` is acceptable for the Lucas-Lehmer test on `Mₙ` (Assertion A: the
test diagnoses primality of `Mₙ`) when the two Jacobi-symbol conditions hold.
Here `Mₙ = mersenne n` and `sₙ₋₁` is the `(n - 2)`-fold iterate of
`x ↦ x^2 - 2` starting from `s₁`.

Source: E. L. Roettger and H. C. Williams, "Some Remarks Concerning the
Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025),
Article 25.2.5, Theorem (label acceptableseed), lines 814–819; Assertion A
(label assertionA) at lines 187–190,
https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex

Proves `Wanted` entry `acceptableSeed_of_jacobi`.

Proof: Following Mathlib's Lucas-Lehmer order argument, sufficiency uses a quadratic extension
and the least prime factor; necessity uses the Jacobi conditions and Frobenius conjugation as in
Lehmer (1930) and Roettger-Williams (2025).
-/
theorem acceptableSeed_of_jacobi
    (n : ℕ) (hn_odd : Odd n) (hn_ge : 3 ≤ n) (s₁ : ℤ) :
    jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
      jacobiSym (s₁ - 2) (mersenne n) = 1 →
        (Nat.Prime (mersenne n) ↔
          (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁) := by
  intro hjac
  constructor
  · exact lucasLehmerSeed_necessity n hn_odd hn_ge s₁ hjac
  · exact lucasLehmerSeed_sufficiency n hn_ge s₁

end MetaMathlibExt
