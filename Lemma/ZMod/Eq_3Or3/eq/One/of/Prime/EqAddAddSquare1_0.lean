import Mathlib
import sympy.Basic


/--
[ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero.lean)
-/
@[main]
private lemma main
  {M : ℕ}
  {x : ZMod M}
  {ℓ : ℕ}
-- given
  (hx : x ^ 2 + x + 1 = 0)
  (hℓ : ℓ.Prime)
  (hℓM : ℓ ∣ M) :
-- imply
  ℓ = 3 ∨ ℓ % 3 = 1 := by
-- proof
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set y : ZMod ℓ := ZMod.castHom hℓM (ZMod ℓ) x with hy
  have hy0 : y ^ 2 + y + 1 = 0 := by
    have := congrArg (ZMod.castHom hℓM (ZMod ℓ)) hx
    rw [map_add, map_add, map_pow, map_one, map_zero] at this
    exact this
  by_cases h3 : ℓ = 3
  · exact Or.inl h3
  right
  have hy3 : y ^ 3 = 1 := by
    have : y ^ 3 - 1 = (y - 1) * (y ^ 2 + y + 1) := by ring
    rw [hy0, mul_zero, sub_eq_zero] at this
    exact this
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1] at hy0
    norm_num at hy0

    have h3' : (3 : ZMod ℓ) = 0 := by exact_mod_cast hy0
    rw [show (3 : ZMod ℓ) = ((3 : ℕ) : ZMod ℓ) by norm_num, ZMod.natCast_eq_zero_iff] at h3'
    exact h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3')
  have hyne : y ≠ 0 := by
    intro h0; rw [h0] at hy3; norm_num at hy3
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hdvd : 3 ∣ ℓ - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hyne)
  have h2 := hℓ.two_le
  omega


-- created on 2026-10-05
