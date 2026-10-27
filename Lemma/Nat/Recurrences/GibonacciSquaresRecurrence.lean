import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[gibonacci_sq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GibonacciSquaresRecurrence.lean)
-/
@[path]
lemma gibonacci_sq_recurrence
  {g : ℕ → ℤ}
  {n : ℕ}
-- given
  (hg : ∀ n : ℕ, g (n + 2) = g (n + 1) + g n) :
-- imply
  g (n + 3) ^ 2 = (Nat.fib 3 : ℤ) * g (n + 2) ^ 2 +
      (Nat.fib 3 : ℤ) * g (n + 1) ^ 2 - g n ^ 2 := by
-- proof
  have h0 := hg n
  have h1 := hg (n + 1)
  have e1 : n + 1 + 2 = n + 3 := by omega
  have e2 : n + 1 + 1 = n + 2 := by omega
  rw [e1, e2] at h1
  have hfib : (Nat.fib 3 : ℤ) = 2 := by decide
  rw [hfib, h1, h0]
  ring

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
