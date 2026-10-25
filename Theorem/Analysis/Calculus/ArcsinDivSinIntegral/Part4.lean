/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.BigOperators.Fin
import Def.Analysis.Calculus.ArcsinDivSinIntegral.Part4
/-!
# Bhandari's arcsine-over-sine integral

This file evaluates an integral involving `arcsin (sin x ^ 2)` in terms of Catalan's constant
and two reciprocal-square series.
-/


namespace Real.Calculus.ArcsinDivSinIntegral

open Filter MeasureTheory Topology

open scoped BigOperators Interval

noncomputable section

lemma ads_residue_summable (j : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((8 * n + j : ℕ) : ℝ) ^ 2)) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hinj : Function.Injective (fun n : ℕ => 8 * n + j) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel hab)
  simpa [Function.comp_def] using h.comp_injective hinj

lemma ads_sin_residue_one (n : ℕ) :
    Real.sin (((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4)) = Real.sqrt 2 / 2 := by
  have harg : ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) =
      Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_four]

lemma ads_sin_residue_three (n : ℕ) :
    Real.sin (((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4)) = Real.sqrt 2 / 2 := by
  have harg : ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4) =
      3 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]

lemma ads_sin_residue_five (n : ℕ) :
    Real.sin (((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  have harg : ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4) =
      5 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi, Real.sin_pi_div_four]

lemma ads_sin_residue_seven (n : ℕ) :
    Real.sin (((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4)) = -(Real.sqrt 2 / 2) := by
  have harg : ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4) =
      7 * Real.pi / 4 + (n : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi,
    show 7 * Real.pi / 4 = 3 * Real.pi / 4 + Real.pi by ring,
    Real.sin_add_pi,
    show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.sin_pi_sub, Real.sin_pi_div_four]

lemma ads_SineTerm_summable (x : ℝ) : Summable (adsSineTerm x) := by
  unfold adsSineTerm
  simpa only [one_pow, one_mul] using
    ads_Sr_summable (1 : ℝ) x (by norm_num) (by norm_num)

lemma ads_tsum_mod_four {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n : ℕ, f n) =
      ((∑' n : ℕ, f (4 * n)) + ∑' n : ℕ, f (4 * n + 2)) +
        ((∑' n : ℕ, f (4 * n + 1)) + ∑' n : ℕ, f (4 * n + 3)) := by
  rw [Nat.sumByResidueClasses hf 4]
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp, Fin.sum_univ_four]
  change ((∑' m : ℕ, f (0 + 4 * m)) + (∑' m : ℕ, f (1 + 4 * m)) +
    (∑' m : ℕ, f (2 + 4 * m)) + ∑' m : ℕ, f (3 + 4 * m)) = _
  ring_nf

lemma ads_SineTerm_pi_div_eight_residue_one (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n) = Real.sqrt 2 / 2 *
      ((1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n) + 1 = 8 * n + 1 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 1 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_one]
  ring

lemma ads_SineTerm_pi_div_eight_residue_three (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 1) = Real.sqrt 2 / 2 *
      ((1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 1) + 1 = 8 * n + 3 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 3 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_three]
  ring

lemma ads_SineTerm_pi_div_eight_residue_five (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 2) = -(Real.sqrt 2 / 2) *
      ((1 : ℝ) / (((8 * n + 5 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 2) + 1 = 8 * n + 5 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 5 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_five]
  ring

lemma ads_SineTerm_pi_div_eight_residue_seven (n : ℕ) :
    adsSineTerm (Real.pi / 8) (4 * n + 3) = -(Real.sqrt 2 / 2) *
      ((1 : ℝ) / (((8 * n + 7 : ℕ) : ℝ) ^ 2)) := by
  unfold adsSineTerm
  have hk : 2 * (4 * n + 3) + 1 = 8 * n + 7 := by omega
  rw [hk]
  have harg : 2 * ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 8) =
      ((8 * n + 7 : ℕ) : ℝ) * (Real.pi / 4) := by ring
  rw [harg, ads_sin_residue_seven]
  ring

lemma ads_tsum_SineTerm_pi_div_eight_residue_one :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n)) =
      Real.sqrt 2 / 2 * adsResidueSum 1 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_one, tsum_mul_left]

lemma ads_tsum_SineTerm_pi_div_eight_residue_three :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 1)) =
      Real.sqrt 2 / 2 * adsResidueSum 3 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_three, tsum_mul_left]

lemma ads_tsum_SineTerm_pi_div_eight_residue_five :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 2)) =
      -(Real.sqrt 2 / 2) * adsResidueSum 5 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_five, tsum_mul_left]

lemma ads_tsum_SineTerm_pi_div_eight_residue_seven :
    (∑' n : ℕ, adsSineTerm (Real.pi / 8) (4 * n + 3)) =
      -(Real.sqrt 2 / 2) * adsResidueSum 7 := by
  unfold adsResidueSum
  simp_rw [ads_SineTerm_pi_div_eight_residue_seven, tsum_mul_left]

lemma ads_SineSeries_pi_div_eight :
    adsSineSeries (Real.pi / 8) = Real.sqrt 2 / 2 *
      (adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 - adsResidueSum 7) := by
  rw [adsSineSeries, ads_tsum_mod_four (ads_SineTerm_summable (Real.pi / 8)),
    ads_tsum_SineTerm_pi_div_eight_residue_one,
    ads_tsum_SineTerm_pi_div_eight_residue_three,
    ads_tsum_SineTerm_pi_div_eight_residue_five,
    ads_tsum_SineTerm_pi_div_eight_residue_seven]
  ring

lemma ads_logTanIntegral_pi_div_eight :
    adsLogTanIntegral (Real.pi / 8) = -(Real.sqrt 2 / 2 *
      (adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 -
        adsResidueSum 7)) := by
  rw [ads_logTanIntegral_eq_neg_sineSeries
    (show Real.pi / 8 ∈ Set.Icc (0 : ℝ) (Real.pi / 4) by
      constructor <;> linarith [Real.pi_pos]),
    ads_SineSeries_pi_div_eight]

lemma ads_all_inv_sq_summable :
    Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

lemma ads_even_inv_sq_summable :
    Summable (fun n : ℕ => (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2)) := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.mul_left_cancel (by norm_num) hab
  simpa only [Function.comp_def] using ads_all_inv_sq_summable.comp_injective hinj

lemma ads_even_inv_sq_tsum :
    (∑' n : ℕ, (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2)) =
      (1 / 4 : ℝ) * ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ 2) := by
  have hterm (n : ℕ) : (1 : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2) =
      (1 / 4 : ℝ) * ((1 : ℝ) / ((n : ℝ) ^ 2)) := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
        push_cast
        ring
      rw [hcast]
      field_simp
      ring
  simp_rw [hterm, tsum_mul_left]

lemma ads_odd_inv_sq_tsum :
    (∑' n : ℕ, (1 : ℝ) / (((2 * n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi ^ 2 / 8 := by
  have hzeta : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) ^ 2)) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  have hsplit := tsum_even_add_odd
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))
    ads_even_inv_sq_summable ads_base_summable
  rw [ads_even_inv_sq_tsum, hzeta] at hsplit
  linarith [sq_pos_of_pos Real.pi_pos]

lemma ads_base_residue_one :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 1 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n) + 1 = 8 * n + 1 by omega]

lemma ads_base_residue_three :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 1) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 3 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 1) + 1 = 8 * n + 3 by omega]

lemma ads_base_residue_five :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 2) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 5 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 2) + 1 = 8 * n + 5 by omega]

lemma ads_base_residue_seven :
    (∑' n : ℕ, (1 : ℝ) / (((2 * (4 * n + 3) + 1 : ℕ) : ℝ) ^ 2)) =
      adsResidueSum 7 := by
  unfold adsResidueSum
  apply tsum_congr
  intro n
  rw [show 2 * (4 * n + 3) + 1 = 8 * n + 7 by omega]

lemma ads_residue_sum_total :
    adsResidueSum 1 + adsResidueSum 3 + adsResidueSum 5 + adsResidueSum 7 =
      Real.pi ^ 2 / 8 := by
  have h := ads_tsum_mod_four ads_base_summable
  rw [ads_odd_inv_sq_tsum, ads_base_residue_one, ads_base_residue_three,
    ads_base_residue_five, ads_base_residue_seven] at h
  linarith

lemma ads_shifted_tsum_one :
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) =
      64 * adsResidueSum 1 := by
  unfold adsResidueSum
  calc
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) =
        ∑' n : ℕ, 64 * ((1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      push_cast
      have h : 8 * (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    _ = 64 * ∑' n : ℕ, (1 : ℝ) / (((8 * n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_mul_left

lemma ads_shifted_tsum_three :
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2)) =
      64 * adsResidueSum 3 := by
  unfold adsResidueSum
  calc
    (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2)) =
        ∑' n : ℕ, 64 * ((1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2)) := by
      apply tsum_congr
      intro n
      push_cast
      have h : 8 * (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp
      ring
    _ = 64 * ∑' n : ℕ, (1 : ℝ) / (((8 * n + 3 : ℕ) : ℝ) ^ 2) :=
      tsum_mul_left

/-- Source: Narendra Bhandari, "Infinite Series Associated with the Ratio and
Product of Central Binomial Coefficients", Journal of Integer Sequences 25
(2022), equation (36), lines 307--309,
<https://cs.uwaterloo.ca/journals/JIS/VOL25/Bhandari/bhan8.tex>.

Catalan's constant `G` and the trigamma values `ψ₁(1/8)`, `ψ₁(3/8)` are
expanded as the defining `tsum`s.

Proves `Wanted` entry `arcsin_div_sin_integral`.

Proof: The route follows Bhandari's reduction to log-tangent integrals, followed by an
Abel-regularized Fourier expansion and residue-class evaluation.
-/
theorem arcsin_div_sin_integral : ∫ x in (0 : ℝ)..(Real.pi / 2), Real.arcsin
  ((Real.sin x) ^ 2) / Real.sin x = -2 * tsum
  (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) - Real.pi ^ 2 / (2 * Real.sqrt 2) + 1 /
  (8 * Real.sqrt 2) *
  (tsum (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) + tsum
  (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2))) := by
  rw [ads_integral_eq_logTan_values, ads_logTanIntegral_pi_div_eight,
    ads_logTanIntegral_pi_div_four, ads_shifted_tsum_one, ads_shifted_tsum_three]
  have hsum := ads_residue_sum_total
  have hdiff : adsResidueSum 1 + adsResidueSum 3 - adsResidueSum 5 -
      adsResidueSum 7 =
        2 * (adsResidueSum 1 + adsResidueSum 3) - Real.pi ^ 2 / 8 := by
    linarith
  rw [hdiff]
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [ne_of_gt hsqrt_pos]
  ring_nf
  rw [hsqrt_sq]
  ring

end
end Real.Calculus.ArcsinDivSinIntegral
