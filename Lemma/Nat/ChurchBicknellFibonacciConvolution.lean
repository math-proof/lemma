import Mathlib
import sympy.Basic
import Def.NumberTheory.LucasSequence
import Lemma.Nat.LucasSequence
open Real
open scoped goldenRatio


namespace MetaMathlibExt

/--
[sqrt5_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma sqrt5_ne
  :
-- imply
  √5 ≠ (0 : ℝ) :=
-- proof
  Real.sqrt_ne_zero'.mpr (by norm_num)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cb_lucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma cb_lucas_zero
  :
-- imply
  lucasNumber 0 = 2 := by
-- proof
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cb_lucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma cb_lucas_one
  :
-- imply
  lucasNumber 1 = 1 := by
-- proof
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cb_lucas_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma cb_lucas_add_two
  {n : ℕ} :
-- imply
  lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber n := by
-- proof
  simp [lucasNumber]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cb_lucas_binet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma cb_lucas_binet
  {n : ℕ} :
-- imply
  φ ^ n + ψ ^ n = (lucasNumber n : ℝ) := by
-- proof
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [pow_zero, pow_zero, cb_lucas_zero, Nat.cast_ofNat]
    norm_num
  | one =>
    rw [pow_one, pow_one, goldenRatio_add_goldenConj, cb_lucas_one,
      Nat.cast_one]
  | more n ih1 ih2 =>
    have eα : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
      calc φ ^ (n + 2) = φ ^ n * φ ^ 2 := by rw [pow_add]
        _ = φ ^ n * (φ + 1) := by rw [goldenRatio_sq]
        _ = φ ^ (n + 1) + φ ^ n := by rw [mul_add, mul_one, ← pow_succ]
    have eβ : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
      calc ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by rw [pow_add]
        _ = ψ ^ n * (ψ + 1) := by rw [goldenConj_sq]
        _ = ψ ^ (n + 1) + ψ ^ n := by rw [mul_add, mul_one, ← pow_succ]
    have key : (φ ^ (n + 1) + φ ^ n) + (ψ ^ (n + 1) + ψ ^ n)
      = (φ ^ (n + 1) + ψ ^ (n + 1)) + (φ ^ n + ψ ^ n) := by
      ring
    have hL : lucasNumber (n + 1) + lucasNumber n = lucasNumber (n + 2) :=
      (cb_lucas_add_two n).symm
    rw [eα, eβ, key, ih1, ih2, ← Nat.cast_add, hL]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cb_keyR](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma cb_keyR
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) =
    ((2 : ℝ) ^ n * (lucasNumber n : ℝ) - 2) / 5 := by
-- proof
  have hD : ∀ k, φ ^ k - ψ ^ k = √5 * (Nat.fib k : ℝ) := by
    intro k
    have h1 : (φ ^ k - ψ ^ k) = (Nat.fib k : ℝ) * √5 :=
      (div_eq_iff sqrt5_ne).mp (coe_fib_eq k).symm
    rwa [mul_comm]
  have hsq5 : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have h5 : ∀ k ∈ Finset.range (n + 1),
    5 * ((Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
    = (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
      * (φ ^ (n - k) - ψ ^ (n - k)) := by
    intro k _
    rw [hD k, hD (n - k)]
    calc 5 * ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
      = ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) * 5 := by
        ring
      _ = ((n.choose k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ)) * √5 ^ 2 := by
        rw [hsq5]
      _ = (n.choose k : ℝ) * (√5 * (Nat.fib k : ℝ))
        * (√5 * (Nat.fib (n - k) : ℝ)) := by
        ring
  have hsum : 5 * (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (Nat.fib k : ℝ) * (Nat.fib (n - k) : ℝ))
    = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
        * (φ ^ (n - k) - ψ ^ (n - k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h5
  have h2c : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have sA : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * φ ^ n)
    = 2 ^ n * φ ^ n := by
    rw [← Finset.sum_mul, h2c]
  have sD : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * ψ ^ n)
    = 2 ^ n * ψ ^ n := by
    rw [← Finset.sum_mul, h2c]
  have sB : (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k))
    = (φ + ψ) ^ n := by
    have h := add_pow φ ψ n
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have sC : (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k))
    = (φ + ψ) ^ n := by
    have h := add_pow ψ φ n
    rw [add_comm ψ φ] at h
    rw [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have e1 : ∀ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
      * (φ ^ (n - k) - ψ ^ (n - k))
    = (Nat.choose n k : ℝ) * φ ^ n
      - (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k)
      - (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k)
      + (Nat.choose n k : ℝ) * ψ ^ n := by
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    have hkn' : k + (n - k) = n := by omega
    have eα : φ ^ k * φ ^ (n - k) = φ ^ n := by
      rw [← pow_add, hkn']
    have eβ : ψ ^ k * ψ ^ (n - k) = ψ ^ n := by
      rw [← pow_add, hkn']
    have eDD : (φ ^ k - ψ ^ k) * (φ ^ (n - k) - ψ ^ (n - k))
      = φ ^ n - φ ^ k * ψ ^ (n - k) - ψ ^ k * φ ^ (n - k)
        + ψ ^ n := by
      linear_combination eα + eβ
    calc (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
      * (φ ^ (n - k) - ψ ^ (n - k))
      = (Nat.choose n k : ℝ)
        * ((φ ^ k - ψ ^ k) * (φ ^ (n - k) - ψ ^ (n - k))) := by
        ring
      _ = (Nat.choose n k : ℝ) * (φ ^ n - φ ^ k * ψ ^ (n - k)
        - ψ ^ k * φ ^ (n - k) + ψ ^ n) := by
        rw [eDD]
      _ = (Nat.choose n k : ℝ) * φ ^ n
        - (Nat.choose n k : ℝ) * φ ^ k * ψ ^ (n - k)
        - (Nat.choose n k : ℝ) * ψ ^ k * φ ^ (n - k)
        + (Nat.choose n k : ℝ) * ψ ^ n := by
        ring
  have hsum2 : (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) * (φ ^ k - ψ ^ k)
      * (φ ^ (n - k) - ψ ^ (n - k)))
    = 2 ^ n * (φ ^ n + ψ ^ n) - 2 := by
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, sA, sB, sC, sD, goldenRatio_add_goldenConj]
    simp only [one_pow]
    ring
  have hL := cb_lucas_binet n
  rw [eq_div_iff (by norm_num : (5 : ℝ) ≠ 0)]
  have h2 := hsum
  rw [hsum2, hL] at h2
  linear_combination h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[church_bicknell_fibonacci_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ChurchBicknellFibonacciConvolution.lean)
-/
@[path]
lemma church_bicknell_fibonacci_convolution
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℚ) * Nat.fib k * Nat.fib (n - k)) =
    (((2 : ℚ) ^ n * lucasNumber n - 2) / 5) := by
-- proof
  refine Rat.cast_injective (α := ℝ) ?_
  push_cast
  exact cb_keyR n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
