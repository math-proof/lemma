import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinomialFibonacciConvolution
open MetaMathlibExt


/--
[choose_succ_int](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialFibonacciConvolution.lean)
-/
@[path]
private lemma choose_succ_int_eq
  {n i : ℕ} :
-- imply
  (Nat.choose (n + 1) (i + 1) : ℤ) =
    (Nat.choose n i : ℤ) + (Nat.choose n (i + 1) : ℤ) := by
-- proof
  apply MetaMathlibExt.choose_succ_int n i

/--
[fib_conv_step](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialFibonacciConvolution.lean)
-/
@[path]
private lemma fib_conv_step_eq
  {n k i : ℕ}
-- given
  (hi : i ≤ n) :
-- imply
  (Nat.fib (2 * n + 2 - i + k) : ℤ) - (Nat.fib (2 * n + 1 - i + k) : ℤ) =
    (Nat.fib (2 * n - i + k) : ℤ) := by
-- proof
  apply MetaMathlibExt.fib_conv_step n k i hi

/--
[binomial_fibonacci_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialFibonacciConvolution.lean)
-/
@[path]
private lemma binomial_fibonacci_convolution_eq
  {n k : ℕ} :
-- imply
  Finset.sum (Finset.range (n + 1)) (fun i =>
    (-1 : ℤ) ^ i * (Nat.fib (2 * n - i + k) : ℤ) * (Nat.choose n i : ℤ)) =
    (Nat.fib k : ℤ) := by
-- proof
  apply MetaMathlibExt.binomial_fibonacci_convolution n k


-- created on 2026-10-20
