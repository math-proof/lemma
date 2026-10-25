import Mathlib
import sympy.Basic
import Def.NumberTheory.GibonacciNumber
open MetaMathlibExt


namespace MetaMathlibExt

/--
[gibonacci_zero_one_eq_fib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciNumber.lean)
-/
@[path]
lemma gibonacci_zero_one_eq_fib
  {n : ℕ} :
-- imply
  gibonacciNumber 0 1 n = (Nat.fib n : ℤ) := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
