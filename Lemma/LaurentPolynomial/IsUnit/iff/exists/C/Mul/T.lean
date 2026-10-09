import Mathlib
import sympy.Basic

open LaurentPolynomial

/--
[LaurentPolynomial_isUnit_iff_exists_C_mul_T](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentPolynomial_isUnit_iff_exists_C_mul_T.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  {f : R[T;T⁻¹]} :
-- imply
  IsUnit f ↔ ∃ (c : Rˣ) (n : ℤ), f = C (c : R) * T n := by
-- proof
  constructor
  · intro hf
    obtain ⟨u, rfl⟩ := hf

    obtain ⟨a, p, hp⟩ := LaurentPolynomial.exists_T_pow (u : R[T;T⁻¹])
    obtain ⟨b, q, hq⟩ := LaurentPolynomial.exists_T_pow (↑u⁻¹ : R[T;T⁻¹])
    have hpq : p * q = Polynomial.X ^ (a + b) := by
      apply Polynomial.toLaurent_injective
      rw [map_mul, hp, hq, Polynomial.toLaurent_X_pow, mul_mul_mul_comm, Units.mul_inv, one_mul,
        ← T_add, Nat.cast_add]

    have hdvd : p ∣ Polynomial.X ^ (a + b) := ⟨q, hpq.symm⟩
    obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).1 hdvd
    obtain ⟨v, hv⟩ := hassoc.symm

    obtain ⟨c, hc, hcv⟩ := Polynomial.isUnit_iff.1 v.isUnit
    obtain ⟨c, rfl⟩ := hc
    refine ⟨c, (i : ℤ) - a, ?_⟩
    have hu : (u : R[T;T⁻¹]) = Polynomial.toLaurent p * T (-(a : ℤ)) := by
      rw [hp, mul_T_assoc, add_neg_cancel, T_zero, mul_one]
    rw [hu, ← hv, ← hcv, mul_comm (Polynomial.X ^ i), map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
      mul_assoc, ← T_add, sub_eq_add_neg]
  · rintro ⟨c, n, rfl⟩
    exact ((Units.isUnit c).map C).mul (isUnit_T n)


-- created on 2026-10-05
