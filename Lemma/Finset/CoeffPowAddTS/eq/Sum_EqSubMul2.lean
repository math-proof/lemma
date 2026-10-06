import Mathlib
import sympy.Basic


/--
[LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentPolynomial_T_one_add_T_neg_one_pow_apply_eq_sum_ite_choose.lean)
-/
@[main]
private lemma main
  [CommSemiring R]
  {k : ℕ}
  {m : ℤ} :
-- imply
  ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial R).coeff m =
      ∑ i ∈ Finset.range (k + 1), if (2 * (i : ℤ) - k = m) then ((k.choose i : ℕ) : R) else 0 := by
-- proof
  classical
  have hcomm : Commute (LaurentPolynomial.T 1 : LaurentPolynomial R) (LaurentPolynomial.T (-1)) :=
    Commute.all _ _
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((LaurentPolynomial.T 1 : LaurentPolynomial R) ^ i * LaurentPolynomial.T (-1) ^ (k - i) *
          (k.choose i : LaurentPolynomial R)) =
        AddMonoidAlgebra.single (2 * (i : ℤ) - k) ((k.choose i : ℕ) : R) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [LaurentPolynomial.T_pow, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add]
    have hexp : (i : ℤ) * 1 + ((k - i : ℕ) : ℤ) * (-1) = 2 * (i : ℤ) - k := by
      push_cast [hik]; ring
    rw [hexp, show ((k.choose i : ℕ) : LaurentPolynomial R) = LaurentPolynomial.C ((k.choose i : ℕ) : R) by
      simp [map_natCast]]
    rw [LaurentPolynomial.single_eq_C_mul_T]
    exact mul_comm _ _
  have hsum : ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ k : LaurentPolynomial R) =
      ∑ i ∈ Finset.range (k + 1), AddMonoidAlgebra.single (2 * (i : ℤ) - k) ((k.choose i : ℕ) : R) := by
    rw [hcomm.add_pow]
    exact Finset.sum_congr rfl hterm
  rw [hsum, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]


-- created on 2026-10-05
