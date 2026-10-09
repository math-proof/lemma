import Mathlib
import sympy.Basic


/--
[ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero.lean)
-/
@[path]
private lemma main
  {M : ℕ}
  {x : ZMod M}
  {ℓ : ℕ}
-- given
  (hx : x ^ 2 + 1 = 0)
  (hℓ : ℓ.Prime)
  (hℓM : ℓ ∣ M) :
-- imply
  ℓ = 2 ∨ ℓ % 4 = 1 := by
-- proof
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set y : ZMod ℓ := ZMod.castHom hℓM (ZMod ℓ) x with hy
  have hy0 : y ^ 2 + 1 = 0 := by
    have := congrArg (ZMod.castHom hℓM (ZMod ℓ)) hx
    rw [map_add, map_pow, map_one, map_zero] at this
    exact this
  have hsq : IsSquare (-1 : ZMod ℓ) := ⟨y, by rw [← sq]; linear_combination -hy0⟩
  have h4 : ℓ % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  rcases hℓ.eq_two_or_odd' with h2 | hodd
  · exact Or.inl h2
  · right
    obtain ⟨k, hk⟩ := hodd
    omega


-- created on 2026-10-05
