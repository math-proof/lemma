import sympy.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
SymPy's `RisingFactorial(x, k)` for integer `k` (`rf(x, -k) = 1 / rf(x - k, k)`), and `binomial(n, k)`
for integer `k` (zero for negative `k`). For natural `k`, `RisingFactorial x k` is
`(ascPochhammer R k).eval x`, which is what lemmas with a natural index use directly.
-/

noncomputable def RisingFactorial {R : Type*} [Field R] (x : R) (k : ℤ) : R :=
  if 0 ≤ k then (ascPochhammer R k.toNat).eval x else 1 / (ascPochhammer R (-k).toNat).eval (x + k)

def Binomial (n : ℕ) (k : ℤ) : ℤ :=
  if 0 ≤ k then (n.choose k.toNat : ℤ) else 0

/-- `RisingFactorial(x, n) = Σ_{k ≤ n} x^k · Stirling1(n, k)` (unsigned Stirling numbers of the first kind). -/
theorem ascPochhammer_eval_eq_sum_stirlingFirst (x : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval x = ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) := by
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

noncomputable def FallingFactorial {R : Type*} [Field R] (x : R) (k : ℤ) : R :=
  if 0 ≤ k then (descPochhammer R k.toNat).eval x else 1 / (descPochhammer R (-k).toNat).eval (x - k)

/-- `FallingFactorial(x, n) = Σ_{k ≤ n} x^k · Stirling1(n, k) · (-1)^(n-k)`. -/
theorem descPochhammer_eval_eq_sum_stirlingFirst (x : ℝ) (n : ℕ) :
    (descPochhammer ℝ n).eval x =
      ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) * (-1) ^ (n - k) := by
  have e := ascPochhammer_eval_neg_eq_descPochhammer ℝ x n
  have s := ascPochhammer_eval_eq_sum_stirlingFirst (-x) n
  have hd : (descPochhammer ℝ n).eval x = (-1) ^ n * (ascPochhammer ℝ n).eval (-x) := by
    rw [e, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [hd, s, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by rw [Finset.mem_range] at hk; omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, neg_pow x k]
  have hk2 : ((-1 : ℝ)) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (x ^ k * (Nat.stirlingFirst (k + j) k : ℝ) * (-1) ^ j) * hk2
