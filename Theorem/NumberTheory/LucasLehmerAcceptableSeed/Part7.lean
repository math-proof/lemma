/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasLehmerAcceptableSeed.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LucasLehmer
import Def.NumberTheory.LucasLehmerAcceptableSeed.Part2
/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/


namespace MetaMathlibExt

@[simp] theorem lucasLehmerSeed_alpha_fst (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_alpha s₁ q).1 = (s₁ : ZMod q) / 2 := rfl

@[simp] theorem lucasLehmerSeed_alpha_snd (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_alpha s₁ q).2 = 1 / 2 := rfl

@[simp] theorem lucasLehmerSeed_beta_fst (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_beta s₁ q).1 = (s₁ : ZMod q) / 2 := rfl

@[simp] theorem lucasLehmerSeed_beta_snd (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_beta s₁ q).2 = -(1 / 2) := rfl

theorem lucasLehmerSeed_two_ne_zero {q : ℕ} [Fact q.Prime] (hq_odd : Odd q) :
    (2 : ZMod q) ≠ 0 := by
  obtain ⟨k, hk⟩ := hq_odd
  intro h
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
  have hq_le : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hq_eq : q = 2 := le_antisymm hq_le (Fact.out : q.Prime).two_le
  subst q
  omega

theorem lucasLehmerSeed_alpha_add_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q =
      (s₁ : lucasLehmerSeed_X s₁ q) := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_add_fst, lucasLehmerSeed_alpha_fst,
      lucasLehmerSeed_beta_fst, lucasLehmerSeed_intCast_fst]
    field_simp [lucasLehmerSeed_two_ne_zero hq_odd]
    ring
  · simp

theorem lucasLehmerSeed_alpha_mul_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_alpha s₁ q * lucasLehmerSeed_beta s₁ q = 1 := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_mul_fst, lucasLehmerSeed_alpha_fst,
      lucasLehmerSeed_beta_fst, lucasLehmerSeed_alpha_snd,
      lucasLehmerSeed_beta_snd, lucasLehmerSeed_one_fst]
    rw [lucasLehmerSeed_D]
    field_simp [lucasLehmerSeed_two_ne_zero hq_odd]
    ring
  · simp
    ring

theorem lucasLehmerSeed_beta_mul_alpha (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_beta s₁ q * lucasLehmerSeed_alpha s₁ q = 1 := by
  rw [mul_comm, lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd]

end MetaMathlibExt
