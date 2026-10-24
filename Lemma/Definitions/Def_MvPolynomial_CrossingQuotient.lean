import Mathlib

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

abbrev CrossingQuotient (t : W) : Type _ :=
  MvPolynomial (Fin 2) W ⧸ Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}

variable {W}

namespace CrossingQuotient

variable (t : W)

abbrev mk : MvPolynomial (Fin 2) W →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.mkₐ W (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)})

theorem mk_apply (p : MvPolynomial (Fin 2) W) :
    mk t p = Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) p := rfl

theorem mk_surjective : Function.Surjective (mk t) := Ideal.Quotient.mkₐ_surjective W _

theorem mk_X_mul_mk_X : mk t (X 0) * mk t (X 1) = algebraMap W (CrossingQuotient W t) t := by
  rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

def monomial (n : ℤ) : CrossingQuotient W t :=
  if 0 ≤ n then mk t (X 0) ^ n.toNat else mk t (X 1) ^ (-n).toNat

theorem monomial_of_nonneg {n : ℤ} (h : 0 ≤ n) : monomial t n = mk t (X 0) ^ n.toNat := if_pos h

theorem monomial_of_neg {n : ℤ} (h : n < 0) : monomial t n = mk t (X 1) ^ (-n).toNat := if_neg (not_le.mpr h)

@[simp] theorem monomial_natCast (n : ℕ) : monomial t (n : ℤ) = mk t (X 0) ^ n := by
  rw [monomial_of_nonneg t (Int.natCast_nonneg n), Int.toNat_natCast]

@[simp] theorem monomial_neg_natCast (n : ℕ) : monomial t (-(n : ℤ)) = mk t (X 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero, pow_zero]
  · rw [monomial_of_neg t (by omega), neg_neg, Int.toNat_natCast]

@[simp] theorem monomial_zero : monomial t 0 = 1 := by
  rw [monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero]

def powMap (e : ℕ) : CrossingQuotient W (t ^ e) →ₐ[W] CrossingQuotient W t :=
  Ideal.Quotient.liftₐ (Ideal.span {(X 0 * X 1 - C (t ^ e) : MvPolynomial (Fin 2) W)})
    (aeval fun i : Fin 2 => mk t (X i) ^ e) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, map_sub, map_mul, aeval_X, aeval_X, aeval_C, ← mul_pow, mk_X_mul_mk_X, ← map_pow, sub_self,
        mul_zero])

theorem powMap_mk (e : ℕ) (p : MvPolynomial (Fin 2) W) :
    powMap t e (mk (t ^ e) p) = aeval (fun i : Fin 2 => mk t (X i) ^ e) p := rfl

@[simp] theorem powMap_mk_X (e : ℕ) (i : Fin 2) : powMap t e (mk (t ^ e) (X i)) = mk t (X i) ^ e := by
  rw [powMap_mk, aeval_X]

end CrossingQuotient

end MvPolynomial

end
