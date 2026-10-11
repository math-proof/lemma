import Mathlib
import sympy.Basic
import sympy.series.formal.NotationsExamples


/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma addition_principle_eq
  [DecidableEq α]
  (A B : Finset α)
  (h : Disjoint A B) :
-- imply
  (A ∪ B).card = A.card + B.card := by
-- proof
  apply AlgebraicCombinatorics.FPS.addition_principle A B h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma multiplication_principle_eq
  (α β : Type*)
  (A : Finset α)
  (B : Finset β) :
-- imply
  (A ×ˢ B).card = A.card * B.card := by
-- proof
  apply AlgebraicCombinatorics.FPS.multiplication_principle A B

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma bijection_principle_eq
  (α β : Type*)
  (A : Finset α)
  (B : Finset β)
  (e : α → β)
  (he : e.Bijective)
  (hst : ∀ i, i ∈ A ↔ e i ∈ B) :
-- imply
  A.card = B.card := by
-- proof
  apply AlgebraicCombinatorics.FPS.bijection_principle A B e he hst

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma card_subsets_eq
  (α : Type*)
  (A : Finset α) :
-- imply
  A.powerset.card = 2 ^ A.card := by
-- proof
  apply AlgebraicCombinatorics.FPS.card_subsets A

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma card_subsets_of_size_eq
  (α : Type*)
  (A : Finset α)
  (k : ℕ) :
-- imply
  (A.powersetCard k).card = A.card.choose k := by
-- proof
  apply AlgebraicCombinatorics.FPS.card_subsets_of_size A k

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_def_formula_eq
  [Field K]
  [CharZero K]
  (r : K)
  (n : ℕ) :
-- imply
  Ring.choose r n = (descPochhammer ℤ n).smeval r / n.factorial := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_def_formula r n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma desc_pochhammer_eq_desc_factorial_eq
  (n k : ℕ) :
-- imply
  (descPochhammer ℤ k).smeval (n : ℤ) = n.descFactorial k := by
-- proof
  apply AlgebraicCombinatorics.FPS.descPochhammer_eq_descFactorial n k

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_factorial_smul_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (r : R)
  (n : ℕ) :
-- imply
  n.factorial • Ring.choose r n = (descPochhammer ℤ n).smeval r := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_factorial_smul r n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_nat_cast_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (n k : ℕ) :
-- imply
  Ring.choose (n : R) k = Nat.choose n k := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_natCast n k

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_zero_right_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (r : R) :
-- imply
  Ring.choose r 0 = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_zero_right r

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_zero_left_pos_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  {k : ℕ}
  (hk : 0 < k) :
-- imply
  Ring.choose (0 : R) k = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_zero_left_pos hk

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_one_right_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (r : R) :
-- imply
  Ring.choose r 1 = r := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_one_right r

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_neg_one_eq
  (k : ℕ) :
-- imply
  Ring.choose (-1 : ℤ) k = (-1 : ℤ) ^ k := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_neg_one k

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_factorial_formula_eq
  {n k : ℕ}
  (h : k ≤ n) :
-- imply
  n.choose k = n.factorial / (k.factorial * (n - k).factorial) := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_factorial_formula h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_two_n_n_eq
  (n : ℕ) :
-- imply
  (2 * n).choose n = (∏ i ∈ Finset.range n, (2 * i + 1)) * 2 ^ n / n.factorial := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_two_n_n_eq n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma pascal_identity_eq
  (m n : ℕ)
  (hn : 0 < n)
  (hm : 0 < m) :
-- imply
  m.choose n = (m - 1).choose (n - 1) + (m - 1).choose n := by
-- proof
  apply AlgebraicCombinatorics.FPS.pascal_identity m n hn hm

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma pascal_identity_ring_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (m : R)
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n := by
-- proof
  apply AlgebraicCombinatorics.FPS.pascal_identity_ring m n hn

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma pascal_identity_succ_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (r : R)
  (k : ℕ) :
-- imply
  Ring.choose (r + 1) (k + 1) = Ring.choose r k + Ring.choose r (k + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.pascal_identity_succ r k

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma pascal_identity_int_eq
  (m : ℤ)
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n := by
-- proof
  apply AlgebraicCombinatorics.FPS.pascal_identity_int m n hn

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma pascal_identity_rat_eq
  (m : ℚ)
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n := by
-- proof
  apply AlgebraicCombinatorics.FPS.pascal_identity_rat m n hn

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_zero_of_lt
  {m n : ℕ}
  (h : m < n) :
-- imply
  m.choose n = 0 := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_zero_of_lt h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_symm_eq
  {n k : ℕ}
  (h : k ≤ n) :
-- imply
  n.choose k = n.choose (n - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_symm h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_symm_add_eq
  (a b : ℕ) :
-- imply
  (a + b).choose a = (a + b).choose b := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_symm_add a b

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_symm_of_eq_add_eq
  {n a b : ℕ}
  (h : n = a + b) :
-- imply
  n.choose a = n.choose b := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_symm_of_eq_add h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma binom_symm_ring_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (n k : ℕ)
  (h : k ≤ n) :
-- imply
  Ring.choose (n : R) k = Ring.choose (n : R) (n - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.binom_symm_ring n k h

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma fibonacci_eq_nat_fib_eq
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.FPS.fibonacci n = Nat.fib n := by
-- proof
  apply AlgebraicCombinatorics.FPS.fibonacci_eq_nat_fib n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma golden_ratio_plus_eq :
-- imply
  AlgebraicCombinatorics.FPS.goldenRatioPlus = Real.goldenRatio := by
-- proof
  apply AlgebraicCombinatorics.FPS.goldenRatioPlus_eq

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma golden_ratio_minus_eq :
-- imply
  AlgebraicCombinatorics.FPS.goldenRatioMinus = Real.goldenConj := by
-- proof
  apply AlgebraicCombinatorics.FPS.goldenRatioMinus_eq

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma fibonacci_gf_eq :
-- imply
  (PowerSeries.mk (fun n => (AlgebraicCombinatorics.FPS.fibonacci n : ℚ)) : PowerSeries ℚ) =
      (PowerSeries.X : PowerSeries ℚ) * ((1 : PowerSeries ℚ) - PowerSeries.X - PowerSeries.X ^ 2)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.FPS.fibonacci_gf

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma fibonacci_binet_eq
  (n : ℕ) :
-- imply
  (AlgebraicCombinatorics.FPS.fibonacci n : ℝ) = (AlgebraicCombinatorics.FPS.goldenRatioPlus ^ n - AlgebraicCombinatorics.FPS.goldenRatioMinus ^ n) / Real.sqrt 5 := by
-- proof
  apply AlgebraicCombinatorics.FPS.fibonacci_binet n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_eq_mathlib_catalan_eq
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.FPS.catalan n = _root_.catalan n := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_eq_mathlib_catalan n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_zero_eq :
-- imply
  AlgebraicCombinatorics.FPS.catalan 0 = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_zero

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_one_eq :
-- imply
  AlgebraicCombinatorics.FPS.catalan 1 = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_one

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_two_eq :
-- imply
  AlgebraicCombinatorics.FPS.catalan 2 = 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_two

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_three_eq :
-- imply
  AlgebraicCombinatorics.FPS.catalan 3 = 5 := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_three

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_recurrence_eq
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  AlgebraicCombinatorics.FPS.catalan n = ∑ k ∈ Finset.range n, AlgebraicCombinatorics.FPS.catalan k * AlgebraicCombinatorics.FPS.catalan (n - 1 - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_recurrence n hn

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_explicit_eq
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.FPS.catalan n = (2 * n).choose n / (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_explicit n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_as_diff_eq
  {n : ℕ}
  (hn : 0 < n) :
-- imply
  AlgebraicCombinatorics.FPS.catalan n = (2 * n).choose n - (2 * n).choose (n - 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_as_diff hn

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_gf_equation_eq :
-- imply
  let C := PowerSeries.mk (fun n => (AlgebraicCombinatorics.FPS.catalan n : ℚ))
  C = 1 + PowerSeries.X * C ^ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_gf_equation

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma catalan_gf_explicit_eq :
-- imply
  (2 : ℚ) • (PowerSeries.mk (fun n => (AlgebraicCombinatorics.FPS.catalan n : ℚ)) * PowerSeries.X) =
    (1 : PowerSeries ℚ) - PowerSeries.mk (fun n => Ring.choose (1/2 : ℚ) n * (-4 : ℚ)^n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.catalan_gf_explicit

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma vandermonde_convolution_eq
  (a b n : ℕ) :
-- imply
  (a + b).choose n = ∑ k ∈ Finset.range (n + 1), a.choose k * b.choose (n - k) := by
-- proof
  apply AlgebraicCombinatorics.FPS.vandermonde_convolution a b n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma example_recurrence_zero_eq :
-- imply
  AlgebraicCombinatorics.FPS.exampleRecurrence 0 = 1 := by
-- proof
  apply AlgebraicCombinatorics.FPS.exampleRecurrence_zero

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma example_recurrence_one_eq :
-- imply
  AlgebraicCombinatorics.FPS.exampleRecurrence 1 = 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.exampleRecurrence_one

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma example_recurrence_two_eq :
-- imply
  AlgebraicCombinatorics.FPS.exampleRecurrence 2 = 5 := by
-- proof
  apply AlgebraicCombinatorics.FPS.exampleRecurrence_two

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma example_recurrence_explicit_eq
  (n : ℕ) :
-- imply
  AlgebraicCombinatorics.FPS.exampleRecurrence n = 2 ^ (n + 1) - (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.FPS.exampleRecurrence_explicit n

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma geometric_series_eq :
-- imply
  (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun _ => (1 : ℚ)) := by
-- proof
  apply AlgebraicCombinatorics.FPS.geometric_series

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma geometric_series_scaled_eq
  (α : ℚ) :
-- imply
  (1 - α • PowerSeries.X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun n => α ^ n) := by
-- proof
  apply AlgebraicCombinatorics.FPS.geometric_series_scaled α

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma deriv_inv_one_minus_x_eq :
-- imply
  PowerSeries.derivative ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹) =
    (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.deriv_inv_one_minus_x

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma sum_n_plus_one_pow_eq :
-- imply
  PowerSeries.mk (fun n => (n + 1 : ℚ)) = (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_n_plus_one_pow

/--
[NotationsExamples](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/NotationsExamples.lean)
-/
@[path]
private lemma sum_n_pow_eq :
-- imply
  PowerSeries.mk (fun n => (n : ℚ)) = PowerSeries.X * (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
-- proof
  apply AlgebraicCombinatorics.FPS.sum_n_pow


-- created on 2026-10-11
