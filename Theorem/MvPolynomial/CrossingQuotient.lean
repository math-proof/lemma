module

public import Mathlib
public import Abbrev.MvPolynomial_CrossingQuotient

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable (W : Type*) [CommRing W]

namespace CrossingQuotient

variable (t : W)

public theorem mk_apply (p : MvPolynomial (Fin 2) W) :
    mk t p = Ideal.Quotient.mk (Ideal.span {(X 0 * X 1 - C t : MvPolynomial (Fin 2) W)}) p := rfl


public theorem mk_surjective : Function.Surjective (mk t) := Ideal.Quotient.mkₐ_surjective W _


public theorem mk_X_mul_mk_X : mk t (X 0) * mk t (X 1) = algebraMap W (CrossingQuotient W t) t := by
  rw [← map_mul, Ideal.Quotient.mkₐ_eq_mk, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq, Ideal.Quotient.eq]
  exact Ideal.subset_span rfl


public theorem monomial_of_nonneg {n : ℤ} (h : 0 ≤ n) : monomial t n = mk t (X 0) ^ n.toNat := if_pos h


public theorem monomial_of_neg {n : ℤ} (h : n < 0) : monomial t n = mk t (X 1) ^ (-n).toNat := if_neg (not_le.mpr h)


@[simp] public theorem monomial_natCast (n : ℕ) : monomial t (n : ℤ) = mk t (X 0) ^ n := by
  rw [monomial_of_nonneg t (Int.natCast_nonneg n), Int.toNat_natCast]


@[simp] public theorem monomial_neg_natCast (n : ℕ) : monomial t (-(n : ℤ)) = mk t (X 1) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero, pow_zero]
  · rw [monomial_of_neg t (by omega), neg_neg, Int.toNat_natCast]


@[simp] public theorem monomial_zero : monomial t 0 = 1 := by
  rw [monomial_of_nonneg t le_rfl, Int.toNat_zero, pow_zero]


public theorem powMap_mk (e : ℕ) (p : MvPolynomial (Fin 2) W) :
    powMap t e (mk (t ^ e) p) = aeval (fun i : Fin 2 => mk t (X i) ^ e) p := rfl


@[simp] public theorem powMap_mk_X (e : ℕ) (i : Fin 2) : powMap t e (mk (t ^ e) (X i)) = mk t (X i) ^ e := by
  rw [powMap_mk, aeval_X]

end CrossingQuotient

end MvPolynomial

end
