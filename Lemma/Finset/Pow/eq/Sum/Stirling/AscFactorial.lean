import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℤ} :
-- imply
  x ^ n = ∑ k < (n + 1), (ascPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) * (-1) ^ (n - k) := by
-- proof
  symm
  have key : ∀ (x : ℤ) (n : ℕ), ∑ k < (n + 1), (descPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) = x ^ n := by
    intro x n
    induction n with
    | zero => simp [Nat.Iio_eq_range]
    | succ n ih =>
      have hD : ∀ k : ℕ, (descPochhammer ℤ k).eval x * x = (descPochhammer ℤ (k + 1)).eval x + k * (descPochhammer ℤ k).eval x := by
        intro k
        rw [descPochhammer_succ_eval]
        ring
      have A : ∑ k < (n + 1 + 1), (descPochhammer ℤ k).eval x * (Nat.stirlingSecond (n + 1) k : ℤ) =
          ∑ j < (n + 1), (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n j : ℤ) +
          ∑ j < (n + 1), ((j : ℤ) + 1) * (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℤ) := by
        simp only [Nat.Iio_eq_range]
        rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.stirlingSecond_succ_succ]
        push_cast
        ring
      have B : ∑ j < (n + 1), ((j : ℤ) + 1) * (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℤ) =
          ∑ k < (n + 1), (k : ℤ) * (descPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) := by
        simp only [Nat.Iio_eq_range]
        rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, add_zero,
          Finset.sum_range_succ']
        simp
      rw [A, B, pow_succ, ← ih, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      linear_combination (-(Nat.stirlingSecond n k : ℤ)) * hD k
  have e := key (-x) n
  rw [show x ^ n = (-1) ^ n * (-x) ^ n by rw [← mul_pow]; ring, ← e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := by simpa using hk
  have ha := ascPochhammer_eval_neg_eq_descPochhammer ℤ (-x) k
  rw [neg_neg] at ha
  have hp : (-1 : ℤ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [ha, hp]
  ring


-- created on 2023-08-26
