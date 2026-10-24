import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
open Chapter3
open Finset BigOperators


namespace Chapter3

/--
[discrete_orthogonality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma discrete_orthogonality
  {n : ℕ}
  {k : ℤ}
-- given
  (hn : 0 < n)
  (hk : ¬ (↑n : ℤ) ∣ k) :
-- imply
  ∑ s : Fin n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  set ω := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hprim : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn0
  have hterm : ∀ s : Fin n,
    Complex.exp (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n) =
      ω ^ (k * ↑(s : ℕ)) := by
    intro s; rw [← Complex.exp_int_mul]; congr 1; push_cast; ring
  simp_rw [hterm]
  have hpow : ∀ s : Fin n,
    ω ^ (k * ↑(s : ℕ)) = (ω ^ k) ^ (s : ℕ) := by
    intro s; rw [_root_.zpow_mul, zpow_natCast]
  simp_rw [hpow]
  have hωk : ω ^ k ≠ 1 := by
    intro h; exact hk ((hprim.zpow_eq_one_iff_dvd k).mp h)
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hωk]
  have : (ω ^ k) ^ n = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hprim.pow_eq_one, one_zpow]
  rw [this, sub_self, zero_div]

end Chapter3

namespace Chapter3

/--
[cos_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma cos_sum_zero
  {n : ℕ}
  {k : ℤ}
-- given
  (hn : 0 < n)
  (hk : ¬ (↑n : ℤ) ∣ k) :
-- imply
  ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  have hre : (∑ s : Fin n, Complex.exp
    (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n)).re = 0 := by
    rw [discrete_orthogonality n hn k hk]; simp
  rw [Complex.re_sum] at hre
  convert hre using 1; apply Finset.sum_congr rfl; intro s _
  set θ : ℝ := 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n
  have : (2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n =
    ↑θ * Complex.I := by simp only [θ]; push_cast; ring
  rw [this, Complex.exp_mul_I]
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im]

end Chapter3

namespace Chapter3

/--
[sin_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma sin_sum_zero
  {n : ℕ}
  {k : ℤ}
-- given
  (hn : 0 < n)
  (hk : ¬ (↑n : ℤ) ∣ k) :
-- imply
  ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  have him : (∑ s : Fin n, Complex.exp
    (2 * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n)).im = 0 := by
    rw [discrete_orthogonality n hn k hk]; simp
  rw [Complex.im_sum] at him
  convert him using 1; apply Finset.sum_congr rfl; intro s _
  set θ : ℝ := 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n
  have : (2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑(s : ℕ) / ↑n =
    ↑θ * Complex.I := by simp only [θ]; push_cast; ring
  rw [this, Complex.exp_mul_I]
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re]

end Chapter3

namespace Chapter3

/--
[not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma not_dvd
  {n : ℕ}
  {k : ℤ}
-- given
  (hk_ne : k ≠ 0)
  (hk_abs : k.natAbs < n) :
-- imply
  ¬ (↑n : ℤ) ∣ k := by
-- proof
  intro ⟨c, hc⟩
  obtain h | h := Int.lt_or_lt_of_ne hk_ne
  · have hc_neg : c ≤ -1 := by
    by_contra hc_ge; push_neg at hc_ge
    linarith [mul_nonneg (show (0 : ℤ) ≤ n from by omega) (show (0 : ℤ) ≤ c from by omega)]
    have : k.natAbs ≥ n := by
      have hk_le : k ≤ -(n : ℤ) := by nlinarith
      omega
    omega
  · exact absurd (Int.le_of_dvd h ⟨c, hc⟩) (by omega)

end Chapter3

namespace Chapter3

/--
[natAbs_coe_add_coe_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma natAbs_coe_add_coe_lt
  {a b n : ℕ}
-- given
  (h : a + b < n) :
-- imply
  ((a : ℤ) + (b : ℤ)).natAbs < n := by
-- proof
  rwa [show (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ) from by push_cast; ring, Int.natAbs_natCast]

end Chapter3

namespace Chapter3

/--
[natAbs_coe_sub_coe_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma natAbs_coe_sub_coe_lt
  {a b n : ℕ}
-- given
  (h : a + b < n) :
-- imply
  ((a : ℤ) - (b : ℤ)).natAbs < n := by
-- proof
omega

end Chapter3

namespace Chapter3

/--
[natAbs_two_mul_coe_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma natAbs_two_mul_coe_lt
  {a n : ℕ}
-- given
  (h : a + a < n) :
-- imply
  (2 * (a : ℤ)).natAbs < n := by
-- proof
omega

end Chapter3

namespace Chapter3

/--
[cos_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma cos_sq_sum
  {n : ℕ}
  {k : ℤ}
-- given
  (hn : 0 < n)
  (hk : ¬ (↑n : ℤ) ∣ (2 * k)) :
-- imply
  ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 = (n : ℝ) / 2 := by
-- proof
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 =
    1 / 2 + Real.cos (2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n) / 2 := by
    intro s
    have h := Real.cos_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have heq : 2 * (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) =
      2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n := by ring
    linarith [heq ▸ h]
  simp_rw [key, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  suffices h : ∑ i : Fin n, Real.cos (2 * Real.pi * (2 * ↑k) * ↑(i : ℕ) / ↑n) / 2 = 0 by
    linarith
  rw [← Finset.sum_div]
  simp_rw [show (2 * ↑k : ℝ) = (↑(2 * k) : ℝ) from by push_cast; ring]
  rw [cos_sum_zero n hn (2 * k) hk, zero_div]

end Chapter3

namespace Chapter3

/--
[sin_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma sin_sq_sum
  {n : ℕ}
  {k : ℤ}
-- given
  (hn : 0 < n)
  (hk : ¬ (↑n : ℤ) ∣ (2 * k)) :
-- imply
  ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 = (n : ℝ) / 2 := by
-- proof
  have key : ∀ s : Fin n,
    Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) ^ 2 =
    1 / 2 - Real.cos (2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n) / 2 := by
    intro s
    have hcos := Real.cos_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have heq : 2 * (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) =
      2 * Real.pi * (2 * ↑k) * ↑(s : ℕ) / ↑n := by ring
    linarith [heq ▸ hcos, Real.sin_sq (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)]
  simp_rw [key, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  suffices h : ∑ i : Fin n, Real.cos (2 * Real.pi * (2 * ↑k) * ↑(i : ℕ) / ↑n) / 2 = 0 by
    linarith
  rw [← Finset.sum_div]
  simp_rw [show (2 * ↑k : ℝ) = (↑(2 * k) : ℝ) from by push_cast; ring]
  rw [cos_sum_zero n hn (2 * k) hk, zero_div]

end Chapter3

namespace Chapter3

/--
[cos_cos_cross_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma cos_cos_cross_sum_zero
  {n : ℕ}
  {k k' : ℤ}
-- given
  (hn : 0 < n)
  (hkm : ¬ (↑n : ℤ) ∣ (k - k'))
  (hkp : ¬ (↑n : ℤ) ∣ (k + k')) :
-- imply
  ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) * Real.cos (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.cos (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.cos (2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n) +
      Real.cos (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.cos_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.cos_sub (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib,
    cos_sum_zero n hn _ hkm, cos_sum_zero n hn _ hkp, add_zero, zero_div]

end Chapter3

namespace Chapter3

/--
[sin_sin_cross_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma sin_sin_cross_sum_zero
  {n : ℕ}
  {k k' : ℤ}
-- given
  (hn : 0 < n)
  (hkm : ¬ (↑n : ℤ) ∣ (k - k'))
  (hkp : ¬ (↑n : ℤ) ∣ (k + k')) :
-- imply
  ∑ s : Fin n, Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) * Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  have key : ∀ s : Fin n,
    Real.sin (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.cos (2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n) -
      Real.cos (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.cos_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.cos_sub (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k - k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    cos_sum_zero n hn _ hkm, cos_sum_zero n hn _ hkp, sub_self, zero_div]

end Chapter3

namespace Chapter3

/--
[cos_sin_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma cos_sin_sum_zero
  {n : ℕ}
  {k k' : ℤ}
-- given
  (hn : 0 < n)
  (hkp : ¬ (↑n : ℤ) ∣ (k + k'))
  (habs : (k' - k).natAbs < n) :
-- imply
  ∑ s : Fin n, Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) * Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) = 0 := by
-- proof
  have key : ∀ s : Fin n,
    Real.cos (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n) *
    Real.sin (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n) =
    (Real.sin (2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n) +
      Real.sin (2 * Real.pi * ↑(k' - k) * ↑(s : ℕ) / ↑n)) / 2 := by
    intro s
    have h1 := Real.sin_add (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
    have h2 := Real.sin_sub (2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n)
      (2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n)
    have hadd : 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n + 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k + k') * ↑(s : ℕ) / ↑n := by push_cast; ring
    have hsub : 2 * Real.pi * ↑k' * ↑(s : ℕ) / ↑n - 2 * Real.pi * ↑k * ↑(s : ℕ) / ↑n =
      2 * Real.pi * ↑(k' - k) * ↑(s : ℕ) / ↑n := by push_cast; ring
    rw [hadd] at h1; rw [hsub] at h2; linarith
  simp_rw [key]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 := sin_sum_zero n hn _ hkp
  obtain heq | hne := eq_or_ne (k' - k) 0
  · simp only [heq, Int.cast_zero, mul_zero, zero_mul, zero_div, Real.sin_zero,
    Finset.sum_const_zero, add_zero] at h1 ⊢
    linarith
  · have h2 := sin_sum_zero n hn _ (not_dvd n _ hne habs)
    linarith

end Chapter3

namespace Chapter3

/--
[sqrt2_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma sqrt2_factor
  {a b : ℝ} :
-- imply
  Real.sqrt 2 * a * (Real.sqrt 2 * b) = 2 * (a * b) := by
-- proof
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have eq : Real.sqrt 2 * a * (Real.sqrt 2 * b) = (Real.sqrt 2 * Real.sqrt 2) * (a * b) := by ring
  rw [eq, h]

end Chapter3

namespace Chapter3

/--
[lemma_3_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean)
-/
@[path]
lemma lemma_3_13
  {n M : ℕ}
-- given
  (hn : 0 < n)
  (hM : M ≤ n - 1) :
-- imply
  (trigDesignMatrix n M).transpose * (trigDesignMatrix n M) = (n : ℝ) • (1 : Matrix (Fin M) (Fin M) ℝ) := by
-- proof
  ext j j'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, trigDesignMatrix]
  by_cases hj0 : j.val = 0
  ·
    simp only [hj0, ↓reduceIte, one_mul]
    by_cases hj'0 : j'.val = 0
    ·
      have hjj' : j = j' := Fin.ext (by omega)
      simp [hj'0, ↓reduceIte, hjj', Finset.sum_const, Finset.card_fin]
    ·
      have hjne : j ≠ j' := fun h => hj'0 (by rw [← h]; exact hj0)
      simp only [hjne, ite_false, mul_zero, hj'0, ↓reduceIte]
      by_cases hj'_odd : j'.val % 2 = 1
      · simp only [hj'_odd, ↓reduceIte, ← Finset.mul_sum]
        have h := cos_sum_zero n hn (((j'.val + 1) / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'_odd, ↓reduceIte, ← Finset.mul_sum]
        have h := sin_sum_zero n hn ((j'.val / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
  · by_cases hj_odd : j.val % 2 = 1
    ·
      simp only [hj0, hj_odd, ↓reduceIte, ite_false]
      by_cases hj'0 : j'.val = 0
      ·
        simp only [hj'0, ↓reduceIte, mul_one, ← Finset.mul_sum]
        have hjne : j ≠ j' := fun h => hj0 (by rw [h]; exact hj'0)
        simp only [hjne, ite_false, mul_zero]
        have h := cos_sum_zero n hn (((j.val + 1) / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'0, ↓reduceIte]
        by_cases hj'_odd : j'.val % 2 = 1
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          by_cases hjj' : j = j'
          ·
            subst hjj'; simp only [ite_true]
            have hndvd := not_dvd n (2 * (((j.val + 1) / 2 : ℕ) : ℤ)) (by omega)
              (natAbs_two_mul_coe_lt (by omega : (j.val+1)/2 + (j.val+1)/2 < n))
            have h := cos_sq_sum n hn (((j.val + 1) / 2 : ℕ) : ℤ) hndvd
            simp only [Int.cast_natCast] at h
            simp_rw [show ∀ x : Fin n,
              Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) *
              Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) =
              Real.cos (2 * Real.pi * ↑((j.val + 1) / 2) * ↑↑x / ↑n) ^ 2
              from fun x => by ring]
            linarith
          ·
            simp only [hjj', ite_false, mul_zero]
            have hk_ne : (((j.val+1)/2 : ℕ) : ℤ) - (((j'.val+1)/2 : ℕ) : ℤ) ≠ 0 := by
              intro h; exact hjj' (Fin.ext (by omega))
            have hkm := not_dvd n _ hk_ne
              (natAbs_coe_sub_coe_lt (by omega : (j.val+1)/2 + (j'.val+1)/2 < n))
            have hkp := not_dvd n _ (by omega : (((j.val+1)/2 : ℕ) : ℤ) + (((j'.val+1)/2 : ℕ) : ℤ) ≠ 0)
              (natAbs_coe_add_coe_lt (by omega : (j.val+1)/2 + (j'.val+1)/2 < n))
            have h := cos_cos_cross_sum_zero n hn _ _ hkm hkp
            simp only [Int.cast_natCast] at h; linarith
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          have hjne : j ≠ j' := by intro h; subst h; omega
          simp only [hjne, ite_false, mul_zero]
          have hkp := not_dvd n _
            (by omega : (((j.val+1)/2 : ℕ) : ℤ) + ((j'.val/2 : ℕ) : ℤ) ≠ 0)
            (natAbs_coe_add_coe_lt (by omega : (j.val+1)/2 + j'.val/2 < n))
          have habs : (((j'.val/2 : ℕ) : ℤ) - (((j.val+1)/2 : ℕ) : ℤ)).natAbs < n := by omega
          have h := cos_sin_sum_zero n hn _ _ hkp habs
          simp only [Int.cast_natCast] at h; linarith
    ·
      simp only [hj0, hj_odd, ↓reduceIte, ite_false]
      by_cases hj'0 : j'.val = 0
      ·
        simp only [hj'0, ↓reduceIte, mul_one, ← Finset.mul_sum]
        have hjne : j ≠ j' := fun h => hj0 (by rw [h]; exact hj'0)
        simp only [hjne, ite_false, mul_zero]
        have h := sin_sum_zero n hn ((j.val / 2 : ℕ) : ℤ)
          (not_dvd n _ (by omega) (by omega))
        simp only [Int.cast_natCast] at h; rw [h, mul_zero]
      · simp only [hj'0, ↓reduceIte]
        by_cases hj'_odd : j'.val % 2 = 1
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          have hjne : j ≠ j' := by intro h; subst h; omega
          simp only [hjne, ite_false, mul_zero]
          simp_rw [show ∀ x : Fin n,
            Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) *
            Real.cos (2 * Real.pi * ↑((j'.val + 1) / 2) * ↑↑x / ↑n) =
            Real.cos (2 * Real.pi * ↑((j'.val + 1) / 2) * ↑↑x / ↑n) *
            Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n)
            from fun x => by ring]
          have hkp := not_dvd n _
            (by omega : (((j'.val+1)/2 : ℕ) : ℤ) + ((j.val/2 : ℕ) : ℤ) ≠ 0)
            (natAbs_coe_add_coe_lt (by omega : (j'.val+1)/2 + j.val/2 < n))
          have habs : (((j.val/2 : ℕ) : ℤ) - (((j'.val+1)/2 : ℕ) : ℤ)).natAbs < n := by omega
          have h := cos_sin_sum_zero n hn _ _ hkp habs
          simp only [Int.cast_natCast] at h; linarith
        ·
          simp only [hj'_odd, ↓reduceIte, sqrt2_factor, ← Finset.mul_sum]
          by_cases hjj' : j = j'
          ·
            subst hjj'; simp only [ite_true]
            have hndvd := not_dvd n (2 * ((j.val / 2 : ℕ) : ℤ)) (by omega)
              (natAbs_two_mul_coe_lt (by omega : j.val/2 + j.val/2 < n))
            have h := sin_sq_sum n hn ((j.val / 2 : ℕ) : ℤ) hndvd
            simp only [Int.cast_natCast] at h
            simp_rw [show ∀ x : Fin n,
              Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) *
              Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) =
              Real.sin (2 * Real.pi * ↑(j.val / 2) * ↑↑x / ↑n) ^ 2
              from fun x => by ring]
            linarith
          ·
            simp only [hjj', ite_false, mul_zero]
            have hk_ne : ((j.val/2 : ℕ) : ℤ) - ((j'.val/2 : ℕ) : ℤ) ≠ 0 := by
              intro h; exact hjj' (Fin.ext (by omega))
            have hkm := not_dvd n _ hk_ne
              (natAbs_coe_sub_coe_lt (by omega : j.val/2 + j'.val/2 < n))
            have hkp := not_dvd n _
              (by omega : ((j.val/2 : ℕ) : ℤ) + ((j'.val/2 : ℕ) : ℤ) ≠ 0)
              (natAbs_coe_add_coe_lt (by omega : j.val/2 + j'.val/2 < n))
            have h := sin_sin_cross_sum_zero n hn _ _ hkm hkp
            simp only [Int.cast_natCast] at h; linarith

end Chapter3


-- created on 2026-10-23
