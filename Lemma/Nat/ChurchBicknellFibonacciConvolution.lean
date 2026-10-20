import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ChurchBicknellFibonacciConvolution
open Real
open scoped goldenRatio
open MetaMathlibExt


/--
[sqrt5_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma sqrt5_ne_eq
  :
-- imply
  √5 ≠ (0 : ℝ) := by
-- proof
  apply MetaMathlibExt.sqrt5_ne

/--
[cb_lucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma cb_lucas_zero_eq
  :
-- imply
  lucasNumber 0 = 2 := by
-- proof
  apply MetaMathlibExt.cb_lucas_zero

/--
[cb_lucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma cb_lucas_one_eq
  :
-- imply
  lucasNumber 1 = 1 := by
-- proof
  apply MetaMathlibExt.cb_lucas_one

/--
[cb_lucas_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma cb_lucas_add_two_eq
  {n : ℕ} :
-- imply
  lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
-- proof
  apply MetaMathlibExt.cb_lucas_add_two n

/--
[cb_lucas_binet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma cb_lucas_binet_eq
  {n : ℕ} :
-- imply
  φ ^ n + ψ ^ n = (lucasNumber n : ℝ) := by
-- proof
  apply MetaMathlibExt.cb_lucas_binet n

/--
[cb_keyR](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma cb_keyR_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) =
    ((2 : ℝ) ^ n * (lucasNumber n : ℝ) - 2) / 5 := by
-- proof
  apply MetaMathlibExt.cb_keyR n

/--
[church_bicknell_fibonacci_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
private lemma church_bicknell_fibonacci_convolution_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℚ) * Nat.fib k * Nat.fib (n - k)) =
    (((2 : ℚ) ^ n * lucasNumber n - 2) / 5) := by
-- proof
  apply MetaMathlibExt.church_bicknell_fibonacci_convolution n


-- created on 2026-10-20
