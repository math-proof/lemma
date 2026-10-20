/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GibonacciSquaresRecurrence.lean -/

import Mathlib.Data.Nat.Fib.Basic

namespace MetaMathlibExt

/-! # Gibonacci squares satisfy a linear recurrence
-/

/--
Squares of any Fibonacci-recurrence (Gibonacci) sequence satisfy the
third-order linear recurrence with coefficients `f_3 = 2`:
`g(n+3)^2 = 2*g(n+2)^2 + 2*g(n+1)^2 - g(n)^2`.

Source: Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci
Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem 2
(label theorem02, equation equation02), lines 149–153,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex

`Nat.fib 3 = 2` is the source's `f_3`. The recurrence's characteristic
polynomial `x^3 - 2x^2 - 2x + 1` has roots `α^2, β^2, -1` where `α, β`
are the Fibonacci roots. Verified computationally on 200 random integer
Gibonacci sequences at `n = 0..9`.
Proves `Wanted` entry `gibonacci_sq_recurrence`.
-/
theorem gibonacci_sq_recurrence
    (g : ℕ → ℤ) (hg : ∀ n : ℕ, g (n + 2) = g (n + 1) + g n) (n : ℕ) :
    g (n + 3) ^ 2 = (Nat.fib 3 : ℤ) * g (n + 2) ^ 2 +
      (Nat.fib 3 : ℤ) * g (n + 1) ^ 2 - g n ^ 2 := by
  have h0 := hg n
  have h1 := hg (n + 1)
  have e1 : n + 1 + 2 = n + 3 := by omega
  have e2 : n + 1 + 1 = n + 2 := by omega
  rw [e1, e2] at h1
  have hfib : (Nat.fib 3 : ℤ) = 2 := by decide
  rw [hfib, h1, h0]
  ring

end MetaMathlibExt
