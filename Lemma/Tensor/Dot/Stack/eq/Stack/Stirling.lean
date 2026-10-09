import sympy.functions.combinatorial.numbers
import Lemma.Finset.Sum.Binom.eq.Mul.Stirling
import sympy.Basic
open Finset Nat


@[path]
private lemma vandermonde
  {d m : ℕ}
  {x : ℝ}
-- given
  (h : d ≤ m) :
-- imply
  (Matrix.of fun (i : Fin d) (j : Fin m) => (j : ℝ) ^ (i : ℕ) * x ^ (j : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (i : ℕ)) * ((j : ℕ).choose i : ℝ)) =
    Matrix.of fun (i j : Fin d) => x ^ (j : ℕ) * ((j : ℕ)! : ℝ) * (Stirling i j : ℝ) := by
-- proof
  ext i j
  have hj := j.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℝ) ^ (i : ℕ) * x ^ k * ((-x) ^ (((j : ℕ) : ℤ) - (k : ℤ)) * ((j : ℕ).choose k : ℝ))) m]
  rw [← Finset.sum_subset (s₁ := Finset.range ((j : ℕ) + 1)) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [mul_assoc, ← Finset.Sum.Binom.eq.Mul.Stirling, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [show (((j : ℕ) : ℤ) - (t : ℤ)) = (((j : ℕ) - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ (j : ℕ))]; ring,
    zpow_natCast, neg_pow, show x ^ (j : ℕ) = x ^ t * x ^ ((j : ℕ) - t) by rw [← pow_add]; congr 1; omega]
  ring


-- created on 2022-01-18
