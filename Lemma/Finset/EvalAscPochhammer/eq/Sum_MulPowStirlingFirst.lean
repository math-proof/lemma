import sympy.functions.combinatorial.integer_factorials
import sympy.Basic


/-- `RisingFactorial(x, n) = Σ_{k ≤ n} x^k · Stirling1(n, k)` (unsigned Stirling numbers of the first kind). -/
@[path]
private lemma main
-- given
  (x : ℝ)
  (n : ℕ) :
-- imply
  (ascPochhammer ℝ n).eval x = ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : ∑ k ∈ Finset.range (n + 1 + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) =
        ∑ j ∈ Finset.range (n + 1), x ^ (j + 1) * (Nat.stirlingFirst n (j + 1) : ℝ) +
          x ^ 0 * (Nat.stirlingFirst n 0 : ℝ) := Finset.sum_range_succ' _ _
    have e2 : ∑ k ∈ Finset.range (n + 1 + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) =
        ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) +
          x ^ (n + 1) * (Nat.stirlingFirst n (n + 1) : ℝ) := Finset.sum_range_succ _ _
    rw [Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, add_zero] at e2
    rw [pow_zero, one_mul] at e1
    have h0 : (n : ℝ) * Nat.stirlingFirst n 0 = 0 := by
      cases n with
      | zero =>
        simp
      | succ m =>
        rw [show Nat.stirlingFirst (m + 1) 0 = 0 from rfl, Nat.cast_zero, mul_zero]
    have z : Nat.stirlingFirst (n + 1) 0 = 0 := rfl
    rw [Finset.sum_range_succ', ascPochhammer_succ_eval, ih]
    simp only [Nat.stirlingFirst_succ_succ, z, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, mul_zero, add_zero]
    have split : ∑ j ∈ Finset.range (n + 1),
        x ^ (j + 1) * ((n : ℝ) * (Nat.stirlingFirst n (j + 1) : ℝ) + (Nat.stirlingFirst n j : ℝ)) =
        n * ∑ j ∈ Finset.range (n + 1), x ^ (j + 1) * (Nat.stirlingFirst n (j + 1) : ℝ) +
          x * ∑ j ∈ Finset.range (n + 1), x ^ j * (Nat.stirlingFirst n j : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [split]
    linear_combination (n : ℝ) * e1 - (n : ℝ) * e2 + h0


-- created on 2026-10-07
