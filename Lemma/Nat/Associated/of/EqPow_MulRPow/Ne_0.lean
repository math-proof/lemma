import Mathlib
import sympy.Basic


/--
[Associated_of_pow_eq_units_mul_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Associated_of_pow_eq_units_mul_pow.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  {a b : R}
  {n : ℕ}
  {u : Rˣ}
-- given
  (hn : n ≠ 0)
  (h : a ^ n = (u : R) * b ^ n) :
-- imply
  Associated a b := by
-- proof
  classical
  let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid

  have hassoc : Associated (a ^ n) (b ^ n) := ⟨u⁻¹, by
    rw [h, mul_comm ((u : R)) (b ^ n), mul_assoc, Units.mul_inv, mul_one]⟩
  by_cases ha : a = 0
  · subst ha
    have hb : b ^ n = 0 := by
      have := hassoc.symm
      rw [zero_pow hn] at this
      exact associated_zero_iff_eq_zero _ |>.mp this
    rw [pow_eq_zero_iff hn] at hb
    rw [hb]
  by_cases hb : b = 0
  · subst hb
    have : a ^ n = 0 := by
      rw [zero_pow hn] at hassoc
      exact associated_zero_iff_eq_zero _ |>.mp hassoc
    exact absurd ((pow_eq_zero_iff hn).mp this) ha
  have key := hassoc.normalizedFactors_eq
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, UniqueFactorizationMonoid.normalizedFactors_pow,
    nsmul_right_inj hn] at key
  exact (UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mpr key


-- created on 2026-10-05
