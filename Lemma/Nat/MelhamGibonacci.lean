import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MelhamGibonacci
open MetaMathlibExt


/--
[melham_fibonacci_gibonacci_sum_of_squares_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
private lemma melham_fibonacci_gibonacci_sum_of_squares_general_eq
  {G : ℤ → ℤ}
  {k : ℤ}
  {n : ℕ}
-- given
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
-- imply
  6 * (∑ j ∈ Finset.range (2 * n), (G (k + j)) ^ 2) ^ 2 =
    (Nat.fib (2 * n) : ℤ) ^ 2 *
    ((G (k + n - 2)) ^ 4 + 4 * (G (k + n - 1)) ^ 4 +
    4 * (G (k + n)) ^ 4 + (G (k + n + 1)) ^ 4) := by
-- proof
  apply MetaMathlibExt.melham_fibonacci_gibonacci_sum_of_squares_general G hG k n

/--
[melham_fibonacci_gibonacci_sum_of_squares](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MelhamGibonacci.lean)
-/
@[path]
private lemma melham_fibonacci_gibonacci_sum_of_squares_eq
  {G : ℤ → ℤ}
  {k : ℤ}
  {n : ℕ}
-- given
  (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j)
  (hG_nonzero : G 0 ≠ 0 ∨ G 1 ≠ 0)
  (hn : 0 < n) :
-- imply
  6 * (∑ j ∈ Finset.range (2 * n), (G (k + j)) ^ 2) ^ 2 =
    (Nat.fib (2 * n) : ℤ) ^ 2 *
    ((G (k + n - 2)) ^ 4 + 4 * (G (k + n - 1)) ^ 4 +
    4 * (G (k + n)) ^ 4 + (G (k + n + 1)) ^ 4) := by
-- proof
  apply MetaMathlibExt.melham_fibonacci_gibonacci_sum_of_squares G hG hG_nonzero k n hn


-- created on 2026-10-20
