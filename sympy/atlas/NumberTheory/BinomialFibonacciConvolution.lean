/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialFibonacciConvolution.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- Pascal's rule over `ℤ`, shifted form: for the successor index the
binomial coefficient splits with no truncated subtraction. -/
theorem choose_succ_int (n i : ℕ) :
    (Nat.choose (n + 1) (i + 1) : ℤ) =
      (Nat.choose n i : ℤ) + (Nat.choose n (i + 1) : ℤ) := by
  exact_mod_cast Nat.choose_succ_succ n i

/-- Fibonacci step used in the convolution: peeling two off the top index
of the upper term and one off the lower term leaves the base term. -/
theorem fib_conv_step (n k i : ℕ) (hi : i ≤ n) :
    (Nat.fib (2 * n + 2 - i + k) : ℤ) - (Nat.fib (2 * n + 1 - i + k) : ℤ) =
      (Nat.fib (2 * n - i + k) : ℤ) := by
  have e1 : 2 * n + 2 - i + k = (2 * n - i + k) + 2 := by omega
  have e2 : 2 * n + 1 - i + k = (2 * n - i + k) + 1 := by omega
  rw [e1, e2, Nat.fib_add_two]
  push_cast
  ring

/-- Binomial convolution of Fibonacci numbers: the `n`-th alternating
binomial transform of `i ↦ fib (2n - i + k)` recovers `fib k`.

Source: Brian Hopkins and Aram Tangboonduangjit, "Scaled Fibonacci- and
Lucas-Producing Rational Polynomials," Journal of Integer Sequences 25 (2022),
Article 22.3.5 (Corollary generalizing Corollary cor51(a), lines 989–1000),
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Hopkins/tang25.tex>.
The sum is the `n`-th forward difference, which telescopes by Pascal's rule and
`fib (m + 2) = fib m + fib (m + 1)`.
Proves `Wanted` entry `binomial_fibonacci_convolution`. -/
theorem binomial_fibonacci_convolution (n k : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun i =>
      (-1 : ℤ) ^ i * (Nat.fib (2 * n - i + k) : ℤ) * (Nat.choose n i : ℤ)) =
    (Nat.fib k : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have pascal : ∀ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (i + 1) * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
          (Nat.choose (n + 1) (i + 1) : ℤ) =
        -((-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
          (Nat.choose n i : ℤ)) -
        ((-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
          (Nat.choose n (i + 1) : ℤ)) := by
      intro i _
      rw [choose_succ_int, pow_succ]
      ring
    -- peel the `i = 0` term, then split with Pascal
    have expand : Finset.sum (Finset.range (n + 1 + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * (n + 1) - i + k) : ℤ) *
            (Nat.choose (n + 1) i : ℤ)) =
        (Nat.fib (2 * (n + 1) + k) : ℤ) -
        Finset.sum (Finset.range (n + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose n i : ℤ)) -
        Finset.sum (Finset.range (n + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose n (i + 1) : ℤ)) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
      have e0 : 2 * (n + 1) - 0 + k = 2 * (n + 1) + k := by omega
      rw [e0]
      have eargs : ∀ i ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ (i + 1) * (Nat.fib (2 * (n + 1) - (i + 1) + k) : ℤ) *
            (Nat.choose (n + 1) (i + 1) : ℤ) =
          (-1 : ℤ) ^ (i + 1) * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose (n + 1) (i + 1) : ℤ) := by
        intro i _
        have harg : 2 * (n + 1) - (i + 1) + k = 2 * n + 2 - (i + 1) + k := by
          omega
        rw [harg]
      rw [Finset.sum_congr rfl eargs, Finset.sum_congr rfl pascal,
        Finset.sum_sub_distrib]
      simp only [Finset.sum_neg_distrib]
      ring
    -- reindex the second sum: shift down recovers the full `n`-level sum
    have reindex : Finset.sum (Finset.range (n + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose n (i + 1) : ℤ)) =
        (Nat.fib (2 * (n + 1) + k) : ℤ) -
        Finset.sum (Finset.range (n + 1)) (fun j =>
          (-1 : ℤ) ^ j * (Nat.fib (2 * n + 2 - j + k) : ℤ) *
            (Nat.choose n j : ℤ)) := by
      have hT : Finset.sum (Finset.range (n + 1 + 1)) (fun j =>
            (-1 : ℤ) ^ j * (Nat.fib (2 * n + 2 - j + k) : ℤ) *
              (Nat.choose n j : ℤ)) =
          Finset.sum (Finset.range (n + 1)) (fun i =>
            (-1 : ℤ) ^ (i + 1) * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
              (Nat.choose n (i + 1) : ℤ)) +
          (Nat.fib (2 * (n + 1) + k) : ℤ) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
        have e0 : 2 * n + 2 - 0 + k = 2 * (n + 1) + k := by ring_nf; omega
        rw [e0]
      have hneg : Finset.sum (Finset.range (n + 1)) (fun i =>
            (-1 : ℤ) ^ (i + 1) * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
              (Nat.choose n (i + 1) : ℤ)) =
          -Finset.sum (Finset.range (n + 1)) (fun i =>
            (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
              (Nat.choose n (i + 1) : ℤ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hlast : Finset.sum (Finset.range (n + 1 + 1)) (fun j =>
            (-1 : ℤ) ^ j * (Nat.fib (2 * n + 2 - j + k) : ℤ) *
              (Nat.choose n j : ℤ)) =
          Finset.sum (Finset.range (n + 1)) (fun j =>
            (-1 : ℤ) ^ j * (Nat.fib (2 * n + 2 - j + k) : ℤ) *
              (Nat.choose n j : ℤ)) := by
        rw [Finset.sum_range_succ]
        simp
      linarith [hT, hneg, hlast]
    -- combine: the difference telescopes to the induction hypothesis
    have combine : Finset.sum (Finset.range (n + 1 + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * (n + 1) - i + k) : ℤ) *
            (Nat.choose (n + 1) i : ℤ)) =
        Finset.sum (Finset.range (n + 1)) (fun j =>
          (-1 : ℤ) ^ j * (Nat.fib (2 * n + 2 - j + k) : ℤ) *
            (Nat.choose n j : ℤ)) -
        Finset.sum (Finset.range (n + 1)) (fun i =>
          (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose n i : ℤ)) := by
      have eargs : ∀ i : ℕ, 2 * (n + 1) - i + k = 2 * n + 2 - i + k := by
        intro i; omega
      simp only [eargs]
      have expand' := expand
      simp only [eargs] at expand'
      linarith [expand', reindex]
    rw [combine, ← Finset.sum_sub_distrib]
    have step : ∀ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - i + k) : ℤ) *
            (Nat.choose n i : ℤ) -
          ((-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
            (Nat.choose n i : ℤ)) =
        (-1 : ℤ) ^ i * (Nat.fib (2 * n - i + k) : ℤ) *
          (Nat.choose n i : ℤ) := by
      intro i hi
      have hi' : i ≤ n := by
        have := Finset.mem_range.mp hi; omega
      have h1 : 2 * n + 1 - i + k = 2 * n + 2 - (i + 1) + k := by omega
      have h2 := fib_conv_step n k i hi'
      rw [h1] at h2
      have hfactor : (-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - i + k) : ℤ) *
              (Nat.choose n i : ℤ) -
            ((-1 : ℤ) ^ i * (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ) *
              (Nat.choose n i : ℤ)) =
          (-1 : ℤ) ^ i * (Nat.choose n i : ℤ) *
            ((Nat.fib (2 * n + 2 - i + k) : ℤ) -
              (Nat.fib (2 * n + 2 - (i + 1) + k) : ℤ)) := by
        ring
      rw [hfactor, h2]
      ring
    rw [Finset.sum_congr rfl step]
    exact ih

end MetaMathlibExt
