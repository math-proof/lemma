/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciNumber.lean -/

import Mathlib.Data.Nat.Fib.Basic

/-!
# Gibonacci numbers

This file formalizes the generalized Fibonacci sequence used by Dan Guyer and
aBa Mbirika, *GCD of Sums of k Consecutive Fibonacci, Lucas, and Generalized
Fibonacci Numbers*:
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Mbirika/mb5.tex>.
-/

namespace MetaMathlibExt

/-- The Gibonacci sequence with integer initial values `G₀` and `G₁`. -/
def gibonacciNumber (G₀ G₁ : ℤ) : ℕ → ℤ
  | 0 => G₀
  | 1 => G₁
  | n + 2 => gibonacciNumber G₀ G₁ (n + 1) + gibonacciNumber G₀ G₁ n

/-- The initial values zero and one recover Mathlib's Fibonacci numbers. -/
theorem gibonacci_zero_one_eq_fib (n : ℕ) :
    gibonacciNumber 0 1 n = (Nat.fib n : ℤ) := by
  have h : ∀ m : ℕ, gibonacciNumber 0 1 m = (Nat.fib m : ℤ) ∧
      gibonacciNumber 0 1 (m + 1) = (Nat.fib (m + 1) : ℤ) := by
    intro m
    induction m with
    | zero => simp [gibonacciNumber, Nat.fib_zero, Nat.fib_one]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hindex : n + 1 + 1 = n + 2 := rfl
      rw [hindex]
      simp only [gibonacciNumber, Nat.fib_add_two, Nat.cast_add, ih.1, ih.2, add_comm]
  exact (h n).1

end MetaMathlibExt
