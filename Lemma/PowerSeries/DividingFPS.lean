import Mathlib
import sympy.Basic
import sympy.series.formal.DividingFPS


/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma inverse_unique_eq
  [CommRing L]
  {a b c : L}
  (hb : a * b = 1)
  (hc : a * c = 1) :
-- imply
  b = c := by
-- proof
  apply AlgebraicCombinatorics.inverse_unique hb hc

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma inverse_unique_of_is_unit_eq
  [CommRing L]
  {a : L}
  (ha : IsUnit a)
  {b : L}
  (hb : a * b = 1) :
-- imply
  b = ha.unit⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.inverse_unique_of_isUnit ha hb

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_inv_eq_one_mul_inv_eq
  [CommRing L]
  (u : Lˣ) :
-- imply
  (u⁻¹ : Lˣ) = 1 * u⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fracs1_inv_eq_one_mul_inv u

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_is_unit_mul_is
  [CommRing L]
  {a b : L}
  (ha : IsUnit a)
  (hb : IsUnit b) :
-- imply
  IsUnit (a * b) := by
-- proof
  apply AlgebraicCombinatorics.fracs1_isUnit_mul ha hb

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_mul_inv_rev_eq
  [CommRing L]
  (u v : Lˣ) :
-- imply
  (u * v)⁻¹ = v⁻¹ * u⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fracs1_mul_inv_rev u v

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_mul_inv_comm_eq
  [CommRing L]
  (u v : Lˣ) :
-- imply
  (u * v)⁻¹ = u⁻¹ * v⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fracs1_mul_inv_comm u v

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_zpow_neg_eq_inv_zpow_eq
  [CommRing L]
  (u : Lˣ)
  (n : ℤ) :
-- imply
  u ^ (-n) = u⁻¹ ^ n := by
-- proof
  apply AlgebraicCombinatorics.fracs1_zpow_neg_eq_inv_zpow u n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_zpow_neg_eq_zpow_inv_eq
  [CommRing L]
  (u : Lˣ)
  (n : ℤ) :
-- imply
  u ^ (-n) = (u ^ n)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fracs1_zpow_neg_eq_zpow_inv u n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_zpow_add_eq
  [CommRing L]
  (u : Lˣ)
  (n m : ℤ) :
-- imply
  u ^ (n + m) = u ^ n * u ^ m := by
-- proof
  apply AlgebraicCombinatorics.fracs1_zpow_add u n m

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_mul_zpow_eq
  [CommRing L]
  (u v : Lˣ)
  (n : ℤ) :
-- imply
  (u * v) ^ n = u ^ n * v ^ n := by
-- proof
  apply AlgebraicCombinatorics.fracs1_mul_zpow u v n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_zpow_mul_eq
  [CommRing L]
  (u : Lˣ)
  (n m : ℤ) :
-- imply
  (u ^ n) ^ m = u ^ (n * m) := by
-- proof
  apply AlgebraicCombinatorics.fracs1_zpow_mul u n m

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_div_add_div_eq
  [CommRing L]
  (a c : Lˣ)
  (b d : L) :
-- imply
  (AlgebraicCombinatorics.divByUnit b a) + (AlgebraicCombinatorics.divByUnit d c) = AlgebraicCombinatorics.divByUnit (b * (c : L) + (a : L) * d) (a * c) := by
-- proof
  apply AlgebraicCombinatorics.fracs1_div_add_div a c b d

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_div_mul_div_eq
  [CommRing L]
  (a c : Lˣ)
  (b d : L) :
-- imply
  (AlgebraicCombinatorics.divByUnit b a) * (AlgebraicCombinatorics.divByUnit d c) = AlgebraicCombinatorics.divByUnit (b * d) (a * c) := by
-- proof
  apply AlgebraicCombinatorics.fracs1_div_mul_div a c b d

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fracs1_div_eq_iff
  [CommRing L]
  (a : Lˣ)
  (b c : L) :
-- imply
  (AlgebraicCombinatorics.divByUnit c a) = b ↔ c = (a : L) * b := by
-- proof
  apply AlgebraicCombinatorics.fracs1_div_eq_iff a b c

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_invertible_iff_constant_coeff_iff
  [CommRing K]
  (a : PowerSeries K) :
-- imply
  IsUnit a ↔ IsUnit (a.constantCoeff) := by
-- proof
  apply AlgebraicCombinatorics.fps_invertible_iff_constantCoeff a

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_invertible_iff_constant_coeff_ne_zero_iff
  [Field F]
  (a : PowerSeries F) :
-- imply
  IsUnit a ↔ a.constantCoeff ≠ 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_invertible_iff_constantCoeff_ne_zero a

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_inv_coeff_zero_eq
  [Field F]
  (f : PowerSeries F) :
-- imply
  PowerSeries.coeff 0 f⁻¹ = (PowerSeries.coeff 0 f)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fps_inv_coeff_zero f

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_inv_coeff_succ_eq
  [Field F]
  (f : PowerSeries F)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) f⁻¹ =
    -(PowerSeries.coeff 0 f)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (k + 1) f *
        PowerSeries.coeff (n - k) f⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fps_inv_coeff_succ f n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_inv_coeff_zero_is_unit_eq
  [Field F]
  (f : PowerSeries F)
  (hf : IsUnit f) :
-- imply
  PowerSeries.coeff 0 (↑hf.unit⁻¹ : PowerSeries F) = (PowerSeries.coeff 0 f)⁻¹ := by
-- proof
  apply AlgebraicCombinatorics.fps_inv_coeff_zero_isUnit f hf

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_inv_coeff_succ_is_unit_eq
  [Field F]
  (f : PowerSeries F)
  (hf : IsUnit f)
  (n : ℕ) :
-- imply
  PowerSeries.coeff (n + 1) (↑hf.unit⁻¹ : PowerSeries F) =
    -(PowerSeries.coeff 0 f)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (k + 1) f *
        PowerSeries.coeff (n - k) (↑hf.unit⁻¹ : PowerSeries F) := by
-- proof
  apply AlgebraicCombinatorics.fps_inv_coeff_succ_isUnit f hf n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_one_plus_x_is_unit_is
  [CommRing K] :
-- imply
  IsUnit (1 + PowerSeries.X : PowerSeries K) := by
-- proof
  apply AlgebraicCombinatorics.fps_onePlusX_isUnit

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_one_plus_x_inv_eq
  [Field F] :
-- imply
  (1 + PowerSeries.X : PowerSeries F)⁻¹ = PowerSeries.mk fun n => (-1 : F) ^ n := by
-- proof
  apply AlgebraicCombinatorics.fps_onePlusX_inv

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma binom_upper_negation_eq
  [CommRing R]
  [BinomialRing R]
  [NatPowAssoc R]
  (r : R)
  (k : ℕ) :
-- imply
  Ring.choose (-r) k = (-1 : R) ^ k * Ring.choose (r + k - 1) k := by
-- proof
  apply AlgebraicCombinatorics.binomUpperNegation r k

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma binom_upper_negation_int_eq
  (n : ℤ)
  (k : ℕ) :
-- imply
  Ring.choose (-n) k = (-1 : ℤ) ^ k * Ring.choose (k + n - 1) k := by
-- proof
  apply AlgebraicCombinatorics.binomUpperNegation_int n k

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_one_plus_x_pow_neg_eq
  [Field F]
  [BinomialRing F]
  (n : ℕ) :
-- imply
  ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
    PowerSeries.mk fun k => (-1 : F) ^ k * Ring.choose ((n : ℤ) + k - 1) k := by
-- proof
  apply AlgebraicCombinatorics.fps_onePlusX_pow_neg n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_one_plus_x_pow_neg'_eq
  [Field F]
  [BinomialRing F]
  (n : ℕ) :
-- imply
  ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
    PowerSeries.mk fun k => (Ring.choose (-(n : ℤ)) k : F) := by
-- proof
  apply AlgebraicCombinatorics.fps_onePlusX_pow_neg' n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_newton_binomial_nat_le
  [CommRing R]
  (n : ℕ) :
-- imply
  (1 + PowerSeries.X : PowerSeries R) ^ n =
    PowerSeries.mk fun k => if k ≤ n then (n.choose k : R) else 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_newtonBinomial_nat n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_newton_binomial_neg_eq
  [Field F]
  [BinomialRing F]
  (n : ℕ) :
-- imply
  ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
    PowerSeries.mk fun k => (Ring.choose (-(n : ℤ)) k : F) := by
-- proof
  apply AlgebraicCombinatorics.fps_newtonBinomial_neg n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma power_series_coeff_div_by_x_eq
  [CommRing K]
  (a : PowerSeries K)
  (ha : a.constantCoeff = 0)
  (n : ℕ) :
-- imply
  (AlgebraicCombinatorics.PowerSeries.divByX a ha).coeff n = a.coeff (n + 1) := by
-- proof
  apply AlgebraicCombinatorics.PowerSeries.coeff_divByX a ha n

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_eq_x_mul_iff
  [CommRing K]
  (a b : PowerSeries K) :
-- imply
  a = PowerSeries.X * b ↔ (a.constantCoeff = 0 ∧
    ∃ h : a.constantCoeff = 0, b = AlgebraicCombinatorics.PowerSeries.divByX a h) := by
-- proof
  apply AlgebraicCombinatorics.fps_eq_X_mul_iff a b

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_x_mul_constant_coeff_zero_eq
  [CommRing K]
  (b : PowerSeries K) :
-- imply
  (PowerSeries.X * b).constantCoeff = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_X_mul_constantCoeff_zero b

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_eq_x_mul_div_by_x_eq
  [CommRing K]
  (a : PowerSeries K)
  (ha : a.constantCoeff = 0) :
-- imply
  a = PowerSeries.X * AlgebraicCombinatorics.PowerSeries.divByX a ha := by
-- proof
  apply AlgebraicCombinatorics.fps_eq_X_mul_divByX a ha

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_div_by_x_x_mul_eq
  [CommRing K]
  (b : PowerSeries K) :
-- imply
  AlgebraicCombinatorics.PowerSeries.divByX (PowerSeries.X * b) (AlgebraicCombinatorics.fps_X_mul_constantCoeff_zero b) = b := by
-- proof
  apply AlgebraicCombinatorics.fps_divByX_X_mul b

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_exists_x_mul_of_constant_coeff_zero_eq
  [CommRing K]
  (a : PowerSeries K)
  (ha : a.constantCoeff = 0) :
-- imply
  ∃ h : PowerSeries K, a = PowerSeries.X * h := by
-- proof
  apply AlgebraicCombinatorics.fps_exists_X_mul_of_constantCoeff_zero a ha

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_coeff_x_pow_mul_eq_zero_eq
  [CommRing K]
  (k : ℕ)
  (a : PowerSeries K)
  (m : ℕ)
  (hm : m < k) :
-- imply
  (PowerSeries.X ^ k * a).coeff m = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_coeff_X_pow_mul_eq_zero k a m hm

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_first_k_coeffs_zero_iff_x_pow_dvd_iff
  [CommRing K]
  (k : ℕ)
  (f : PowerSeries K) :
-- imply
  (∀ m < k, f.coeff m = 0) ↔ PowerSeries.X ^ k ∣ f := by
-- proof
  apply AlgebraicCombinatorics.fps_first_k_coeffs_zero_iff_X_pow_dvd k f

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_coeff_mul_eq_of_coeff_eq
  [CommRing K]
  (a f g : PowerSeries K)
  (n : ℕ)
  (h : ∀ m ≤ n, f.coeff m = g.coeff m) :
-- imply
  ∀ m ≤ n, (a * f).coeff m = (a * g).coeff m := by
-- proof
  apply AlgebraicCombinatorics.fps_coeff_mul_eq_of_coeff_eq a f g n h

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_coeff_zero_of_multiple_le
  [CommRing K]
  (u v : PowerSeries K)
  (n : ℕ)
  (hdvd : u ∣ v)
  (hu : ∀ m ≤ n, u.coeff m = 0) :
-- imply
  ∀ m ≤ n, v.coeff m = 0 := by
-- proof
  apply AlgebraicCombinatorics.fps_coeff_zero_of_multiple u v n hdvd hu

/--
[DividingFPS](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DividingFPS.lean)
-/
@[path]
private lemma fps_coeff_mul_eq_of_both_coeff_eq
  [CommRing K]
  (a b c d : PowerSeries K)
  (n : ℕ)
  (hab : ∀ m ≤ n, a.coeff m = b.coeff m)
  (hcd : ∀ m ≤ n, c.coeff m = d.coeff m) :
-- imply
  ∀ m ≤ n, (a * c).coeff m = (b * d).coeff m := by
-- proof
  apply AlgebraicCombinatorics.fps_coeff_mul_eq_of_both_coeff_eq a b c d n hab hcd


-- created on 2026-10-11
