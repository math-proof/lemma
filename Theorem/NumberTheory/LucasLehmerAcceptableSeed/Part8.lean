/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Def.NumberTheory.LucasLehmerAcceptableSeed.Part3
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_alphaUnit_coe (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    (lucasLehmerSeed_alphaUnit s₁ q hq_odd : lucasLehmerSeed_X s₁ q) =
      lucasLehmerSeed_alpha s₁ q := rfl

theorem lucasLehmerSeed_closedForm (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (j : ℕ) :
    ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁ : ℤ) : lucasLehmerSeed_X s₁ q) =
      lucasLehmerSeed_alpha s₁ q ^ 2 ^ j + lucasLehmerSeed_beta s₁ q ^ 2 ^ j := by
  induction j with
  | zero =>
      simpa using (lucasLehmerSeed_alpha_add_beta s₁ q hq_odd).symm
  | succ j ih =>
      calc
        ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) (j + 1) s₁ : ℤ) :
              lucasLehmerSeed_X s₁ q) =
            ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁) ^ 2 - 2 : ℤ) := by
              rw [Function.iterate_succ_apply']
        _ = ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁ : ℤ) :
              lucasLehmerSeed_X s₁ q) ^ 2 - 2 := by
              push_cast
              rfl
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j +
              lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 - 2 := by rw [ih]
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) ^ 2 +
              (lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 +
              2 * (lucasLehmerSeed_beta s₁ q ^ 2 ^ j *
                lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) - 2 := by ring
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) ^ 2 +
              (lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 := by
              rw [← mul_pow, lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd, one_pow]
              ring
        _ = lucasLehmerSeed_alpha s₁ q ^ 2 ^ (j + 1) +
              lucasLehmerSeed_beta s₁ q ^ 2 ^ (j + 1) := by
              rw [← pow_mul, ← pow_mul, _root_.pow_succ]

theorem lucasLehmerSeed_mersenne_coe_X (s₁ : ℤ) (p : ℕ) :
    (mersenne p : lucasLehmerSeed_X s₁ (Nat.minFac (mersenne p))) = 0 := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_natCast_fst, lucasLehmerSeed_zero_fst]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.minFac_dvd _
  · simp

theorem lucasLehmerSeed_alpha_pow_neg_one (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 1) = -1 := by
  obtain ⟨k, hk⟩ := hdiv
  replace hk := congr_arg (fun z : ℤ => (z : lucasLehmerSeed_X s₁ q)) hk
  rw [lucasLehmerSeed_closedForm s₁ q hq_odd] at hk
  push_cast at hk
  rw [hM] at hk
  simp only [zero_mul] at hk
  have h := congr_arg
    (fun x : lucasLehmerSeed_X s₁ q => lucasLehmerSeed_alpha s₁ q ^ 2 ^ p' * x) hk
  have hexp : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add, ← pow_add, hexp, ← mul_pow, lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd,
    one_pow, mul_zero] at h
  linear_combination h

theorem lucasLehmerSeed_alpha_pow_one (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 2) = 1 := by
  calc
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 2) =
        (lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by
      rw [lucasLehmerSeed_alpha_pow_neg_one p' s₁ q hq_odd hM hdiv]
    _ = 1 := by norm_num

theorem lucasLehmerSeed_order_alpha (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    orderOf (lucasLehmerSeed_alphaUnit s₁ q hq_odd) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  · exact Nat.prime_two
  · intro o
    have halpha := congr_arg
      (Units.coeHom (lucasLehmerSeed_X s₁ q) :
        (lucasLehmerSeed_X s₁ q)ˣ → lucasLehmerSeed_X s₁ q)
      (orderOf_dvd_iff_pow_eq_one.1 o)
    have hbad : (1 : ZMod q) = -1 := congr_arg Prod.fst <|
      halpha.symm.trans (lucasLehmerSeed_alpha_pow_neg_one p' s₁ q hq_odd hM hdiv)
    obtain ⟨k, hk⟩ := hq_odd
    have hq_gt : 2 < q := by
      have := (Fact.out : q.Prime).two_le
      omega
    have : Fact (2 < q) := ⟨hq_gt⟩
    exact ZMod.neg_one_ne_one hbad.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact lucasLehmerSeed_alpha_pow_one p' s₁ q hq_odd hM hdiv

theorem lucasLehmerSeed_order_ineq (p' : ℕ) (s₁ : ℤ)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    2 ^ (p' + 2) < Nat.minFac (mersenne (p' + 2)) ^ 2 := by
  let q := Nat.minFac (mersenne (p' + 2))
  have hq_prime : q.Prime := by
    dsimp [q]
    exact Nat.minFac_prime (ne_of_gt (one_lt_mersenne.2 (by omega)))
  have : Fact q.Prime := ⟨hq_prime⟩
  have hq_gt : 2 < q := by simpa [q] using lucasLehmerSeed_two_lt_minFac p'
  have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
  have hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0 := by
    simpa [q] using lucasLehmerSeed_mersenne_coe_X s₁ (p' + 2)
  calc
    2 ^ (p' + 2) = orderOf (lucasLehmerSeed_alphaUnit s₁ q hq_odd) :=
      (lucasLehmerSeed_order_alpha p' s₁ q hq_odd hM hdiv).symm
    _ ≤ Fintype.card (lucasLehmerSeed_X s₁ q)ˣ := orderOf_le_card_univ
    _ < q ^ 2 := lucasLehmerSeed_card_units_lt s₁ q (by omega)

theorem lucasLehmerSeed_sufficiency (n : ℕ) (hn_ge : 3 ≤ n) (s₁ : ℤ) :
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁ →
      (mersenne n).Prime := by
  set p' := n - 2 with hp'
  clear_value p'
  obtain rfl : n = p' + 2 := by omega
  contrapose
  intro hnot_prime hdiv
  have horder := lucasLehmerSeed_order_ineq p' s₁ hdiv
  have hfactor := Nat.minFac_sq_le_self
    (mersenne_pos.2 (by omega : 0 < p' + 2)) hnot_prime
  have hcontra := lt_of_lt_of_le horder hfactor
  exact not_lt_of_ge (Nat.sub_le _ _) hcontra

end MetaMathlibExt
