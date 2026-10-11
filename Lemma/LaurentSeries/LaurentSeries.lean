import Mathlib
import sympy.Basic
import sympy.series.LaurentSeries


/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma binary_representation_exists_is
-- given
  (n : ℕ) :
-- imply
  Nonempty (AlgebraicCombinatorics.BinaryRepresentation n) := by
-- proof
  apply AlgebraicCombinatorics.binaryRepresentation_exists n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma binary_representation_unique_eq
-- given
  (n : ℕ)
  (r₁ r₂ : AlgebraicCombinatorics.BinaryRepresentation n) :
-- imply
  r₁.bits = r₂.bits := by
-- proof
  apply AlgebraicCombinatorics.binaryRepresentation_unique n r₁ r₂

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_zero_eq :
-- imply
  (0 : AlgebraicCombinatorics.BalancedTernaryDigit).toInt = 0 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_zero

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_injective_is :
-- imply
  Function.Injective AlgebraicCombinatorics.BalancedTernaryDigit.toInt := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_injective

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_range_le
-- given
  (d : AlgebraicCombinatorics.BalancedTernaryDigit) :
-- imply
  -1 ≤ d.toInt ∧ d.toInt ≤ 1 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_range d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_int_mod_three_injective_is :
-- imply
  Function.Injective fun d : AlgebraicCombinatorics.BalancedTernaryDigit => d.toInt % 3 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.toInt_mod_three_injective

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma eq_of_to_int_mod_three_eq_eq
-- given
  (a b : AlgebraicCombinatorics.BalancedTernaryDigit)
  (h : a.toInt % 3 = b.toInt % 3) :
-- imply
  a = b := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.eq_of_toInt_mod_three_eq a b h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma ne_zero_iff_to_int_ne_zero_iff
-- given
  (d : AlgebraicCombinatorics.BalancedTernaryDigit) :
-- imply
  d ≠ 0 ↔ d.toInt ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero d

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_exists_is
-- given
  (n : ℤ) :
-- imply
  Nonempty (AlgebraicCombinatorics.BalancedTernaryRepresentation n) := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_exists n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_unique_eq
-- given
  (n : ℤ)
  (r₁ r₂ : AlgebraicCombinatorics.BalancedTernaryRepresentation n) :
-- imply
  r₁.digits = r₂.digits := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_unique n r₁ r₂

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma ext_eq
  [Semiring K]
-- given
  (f g : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (h : ∀ (n : ℤ), f.coeff n = g.coeff n) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.ext h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_add_eq
  [Semiring K]
-- given
  (f g : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (n : ℤ) :
-- imply
  (f + g).coeff n = f.coeff n + g.coeff n := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_add f g n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_smul_eq
  [Semiring K]
-- given
  (r : K)
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (n : ℤ) :
-- imply
  (r • f).coeff n = r * f.coeff n := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_smul r f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_eq
  [Semiring K]
-- given
  (n m : ℤ) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff m =
    if m = n then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single n m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_zero_eq
  [Semiring K]
-- given
  (n : ℤ) :
-- imply
  (0 : AlgebraicCombinatorics.DoublyInfinitePowerSeries K).coeff n = 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_zero n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma single_zero_eq_one_eq
  [Semiring K] :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.single 0 =
    fun n => if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.single_zero_eq_one

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_self_eq
  [Semiring K]
-- given
  (n : ℤ) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff n = 1 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single_self n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_single_ne_eq
  [Semiring K]
-- given
  (n m : ℤ)
  (h : m ≠ n) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n).coeff m = 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_single_ne h

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma smul_single_eq
  [Semiring K]
-- given
  (r : K)
  (n : ℤ) :
-- imply
  r • AlgebraicCombinatorics.DoublyInfinitePowerSeries.single n =
    fun m => if m = n then r else 0 := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.smul_single r n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma eq_coeff_at_position_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (m : ℤ) :
-- imply
  f m = f.coeff m := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.eq_coeff_at_position f m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma coeff_eq_single_contrib_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (m : ℤ) :
-- imply
  f.coeff m =
    f.coeff m * (AlgebraicCombinatorics.DoublyInfinitePowerSeries.single m).coeff m := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.coeff_eq_single_contrib f m

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma is_laurent_series_support_bdd_below_is
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (hf : f.IsLaurentSeries) :
-- imply
  BddBelow {n : ℤ | f.coeff n ≠ 0} := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.IsLaurentSeries.support_bddBelow hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma is_laurent_series_of_laurent_series_is
  [Semiring K]
-- given
  (f : LaurentSeries K) :
-- imply
  (AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries f).IsLaurentSeries := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.isLaurentSeries_ofLaurentSeries f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma int_is_pwo_of_bdd_below_is
-- given
  (s : Set ℤ)
  (hs : BddBelow s) :
-- imply
  s.IsPWO := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.Int.isPWO_of_bddBelow hs

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma to_laurent_series_of_laurent_series_eq
  [Semiring K]
-- given
  (f : LaurentSeries K) :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries f)
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.isLaurentSeries_ofLaurentSeries f) = f := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries_ofLaurentSeries f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma of_laurent_series_to_laurent_series_eq
  [Semiring K]
-- given
  (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K)
  (hf : f.IsLaurentSeries) :
-- imply
  AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries
    (AlgebraicCombinatorics.DoublyInfinitePowerSeries.toLaurentSeries f hf) = f := by
-- proof
  apply AlgebraicCombinatorics.DoublyInfinitePowerSeries.ofLaurentSeries_toLaurentSeries f hf

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_one_eq_t_zero_eq
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  (1 : LaurentPolynomial K) = LaurentPolynomial.T 0 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_one_eq_T_zero K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_one_apply_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (1 : LaurentPolynomial K).coeff n = if n = 0 then 1 else 0 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_one_apply K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_is_unit_is
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  IsUnit (LaurentPolynomial.T 1 : LaurentPolynomial K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_isUnit K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_is_unit'_is
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  IsUnit (LaurentPolynomial.T n : LaurentPolynomial K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_isUnit' K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_mul_t_neg_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (LaurentPolynomial.T n : LaurentPolynomial K) * LaurentPolynomial.T (-n) = 1 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_mul_T_neg K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_t_neg_mul_t_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (n : ℤ) :
-- imply
  (LaurentPolynomial.T (-n) : LaurentPolynomial K) * LaurentPolynomial.T n = 1 := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_T_neg_mul_T K n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_eq_sum_eq
-- given
  (K : Type*)
  [CommSemiring K]
  (f : LaurentPolynomial K) :
-- imply
  f = f.coeff.sum fun n a => LaurentPolynomial.C a * LaurentPolynomial.T n := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_eq_sum K f

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_eq_group_algebra_eq
-- given
  (K : Type*)
  [CommSemiring K] :
-- imply
  LaurentPolynomial K = AddMonoidAlgebra K ℤ := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_eq_groupAlgebra K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_single_eq
-- given
  (K : Type*)
  [CommRing K]
  (n : ℤ)
  (r : K) :
-- imply
  AlgebraicCombinatorics.laurentPolyToSeries K (AddMonoidAlgebra.single n r) =
    HahnSeries.single n r := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_single K n r

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_coeff_eq
-- given
  (K : Type*)
  [CommRing K]
  (f : LaurentPolynomial K)
  (n : ℤ) :
-- imply
  (AlgebraicCombinatorics.laurentPolyToSeries K f).coeff n = f.coeff n := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_coeff K f n

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_poly_to_series_injective_is
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  Function.Injective (AlgebraicCombinatorics.laurentPolyToSeries K) := by
-- proof
  apply AlgebraicCombinatorics.laurentPolyToSeries_injective K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma laurent_polynomial_embeds_in_laurent_series_is
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  ∃ f : LaurentPolynomial K →+* LaurentSeries K, Function.Injective f := by
-- proof
  apply AlgebraicCombinatorics.laurentPolynomial_embeds_in_laurentSeries K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma one_sub_x_pow_is_unit_is
-- given
  (K : Type*)
  [CommRing K]
  (i : ℕ)
  (hi : 0 < i) :
-- imply
  IsUnit (1 - (PowerSeries.X : PowerSeries K) ^ i) := by
-- proof
  apply AlgebraicCombinatorics.one_sub_X_pow_isUnit K i hi

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma torsion_example_is
  [CommRing K] [Nontrivial K] :
-- imply
  ∃ (p : LaurentPolynomial K) (f : AlgebraicCombinatorics.DoublyInfinitePowerSeries K),
    p ≠ 0 ∧ f ≠ 0 ∧ AlgebraicCombinatorics.laurentPolynomialSmul p f = 0 := by
-- proof
  apply AlgebraicCombinatorics.torsion_example

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma bounded_sum_eq_eq
-- given
  (r : AlgebraicCombinatorics.BalancedTernaryRepresentation n)
  (k : ℕ)
  (hk : r.isBounded k) :
-- imply
  n = ∑ i ∈ Finset.range (k + 1), (r.digits i).toInt * (3 : ℤ) ^ i := by
-- proof
  apply AlgebraicCombinatorics.bounded_sum_eq r k hk

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma sum_powers_of_three_eq_zero_eq
-- given
  (k : ℕ)
  (c : ℕ → ℤ)
  (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
  (hzero : ∀ i > k, c i = 0)
  (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ) ^ i = 0) :
-- imply
  ∀ i, c i = 0 := by
-- proof
  apply AlgebraicCombinatorics.sum_powers_of_three_eq_zero k c hc hzero hsum

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma balanced_ternary_representation_bounded_unique_eq
-- given
  (k : ℕ)
  (n : ℤ)
  (r₁ r₂ : AlgebraicCombinatorics.BalancedTernaryRepresentation n)
  (hn : |n| ≤ ∑ i ∈ Finset.range (k + 1), (3 : ℤ) ^ i)
  (h₀ : r₁.isBounded k)
  (h₁ : r₂.isBounded k) :
-- imply
  r₁.digits = r₂.digits := by
-- proof
  apply AlgebraicCombinatorics.balancedTernaryRepresentation_bounded_unique k n hn r₁ r₂ h₀ h₁

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma one_plus_t_plus_tinv_eq_eq
-- given
  (K : Type*)
  [CommRing K] :
-- imply
  (1 + LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial K) *
    (LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1)) = 1 - LaurentPolynomial.T 3 := by
-- proof
  apply AlgebraicCombinatorics.one_plus_T_plus_Tinv_eq K

/--
[LaurentSeries](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/LaurentSeries.lean)
-/
@[path]
private lemma geom_sum_three_eq
-- given
  (k : ℕ) :
-- imply
  2 * ∑ i ∈ Finset.range (k + 1), (3 : ℤ) ^ i = (3 : ℤ) ^ (k + 1) - 1 := by
-- proof
  apply AlgebraicCombinatorics.geom_sum_three k


-- created on 2026-10-11
