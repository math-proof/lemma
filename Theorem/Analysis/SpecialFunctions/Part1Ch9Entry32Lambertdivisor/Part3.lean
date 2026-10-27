/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem leftTerm_eq_F32term (x : ℝ) (k : ℕ) :
    chapter9Entry32LeftTerm x k
      = bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry32LeftTerm bCoeff32
  field_simp

theorem tsum_left_eq_F32 (x : ℝ) :
    (∑' k : ℕ, chapter9Entry32LeftTerm x k) = F32 (Real.sin (2 * x)) := by
  unfold F32
  apply tsum_congr
  intro k
  exact leftTerm_eq_F32term x k

theorem tanTerm_eq_G32term (x : ℝ) (k : ℕ) :
    chapter9Entry19TanTerm x k
      = (-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry19TanTerm
  ring

theorem tsum_tan_eq_G32 (x : ℝ) :
    (∑' k : ℕ, chapter9Entry19TanTerm x k) = G32 (Real.tan x) := by
  unfold G32
  apply tsum_congr
  intro k
  exact tanTerm_eq_G32term x k

theorem summable_succ_mul_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have heq : (fun n : ℕ => ((n : ℝ) + 1) * r ^ n)
      = fun n : ℕ => (n : ℝ) * r ^ n + r ^ n := by
    funext n
    ring
  rw [heq]
  exact h1.add h0

theorem summable_sq_mul_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) := by
  simpa [Nat.cast_pow] using
    summable_pow_mul_geometric_of_norm_lt_one 2 hr

theorem summable_succ_mul_succ_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * r ^ n) := by
  have h2 := summable_sq_mul_pow32 hr
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have heq : (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * r ^ n)
      = fun n : ℕ => (n : ℝ) ^ 2 * r ^ n + 3 * ((n : ℝ) * r ^ n)
        + 2 * r ^ n := by
    funext n
    ring
  rw [heq]
  exact (h2.add (h1.mul_left 3)).add (h0.mul_left 2)

theorem summable_S32_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => aCoeff32 k * z ^ k) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hz
  have hbase := summable_succ_mul_pow32 (r := ‖z‖) hr
  have hsum : Summable (fun k : ℕ => 2 * (((k : ℝ) + 1) * ‖z‖ ^ k)) :=
    hbase.mul_left 2
  apply Summable.of_norm_bounded hsum
  intro k
  rw [norm_mul, norm_pow]
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  calc ‖aCoeff32 k‖ * ‖z‖ ^ k
      ≤ (2 * ((k : ℝ) + 1)) * ‖z‖ ^ k :=
        mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) _)
    _ = 2 * (((k : ℝ) + 1) * ‖z‖ ^ k) := by ring

theorem S32_zero : S32 0 = 1 := by
  unfold S32
  have hsingle : HasSum (fun k : ℕ => aCoeff32 k * (0 : ℝ) ^ k) 1 := by
    have h0 : aCoeff32 0 * (0 : ℝ) ^ (0 : ℕ) = 1 := by
      rw [aCoeff32_zero]
      norm_num
    have h00 : ∀ b : ℕ, b ≠ 0 → aCoeff32 b * (0 : ℝ) ^ b = 0 := by
      intro b hb
      rw [zero_pow hb]
      ring
    have hS := hasSum_single (0 : ℕ) h00
    rw [h0] at hS
    exact hS
  exact hsingle.tsum_eq

theorem F32_zero : F32 0 = 0 := by
  unfold F32
  have hzero : (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

theorem G32_zero : G32 0 = 0 := by
  unfold G32
  have hzero : (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

theorem summable_F32_zero :
    Summable (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hzero : (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => (0 : ℝ) := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero]
  exact summable_zero

theorem summable_G32_zero :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hzero : (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => (0 : ℝ) := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero]
  exact summable_zero

theorem S32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => aCoeff32 k * z ^ k)
      (aCoeff32 k * (k : ℝ) * y ^ (k - 1)) y := by
  have hpow : HasDerivAt (fun z : ℝ => z ^ k)
      ((k : ℝ) * y ^ (k - 1)) y :=
    hasDerivAt_pow k y
  have hmul := hpow.const_mul (aCoeff32 k)
  have heq : aCoeff32 k * ((k : ℝ) * y ^ (k - 1))
      = aCoeff32 k * (k : ℝ) * y ^ (k - 1) := by ring
  rw [heq] at hmul
  exact hmul

theorem S32_majorant {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff32 k * (k : ℝ) * y ^ (k - 1)‖
      ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have hyrle : ‖y‖ ≤ r := le_of_lt hyr
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  have hk : ‖(k : ℝ)‖ ≤ (k : ℝ) + 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hkn : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow : ‖y‖ ^ (k - 1) ≤ r ^ (k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hyrle _
  have hmain : ‖aCoeff32 k‖ * ‖(k : ℝ)‖ * ‖y‖ ^ (k - 1)
      ≤ (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1) := by
    have h1 : ‖aCoeff32 k‖ * ‖(k : ℝ)‖
        ≤ (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) :=
      mul_le_mul ha hk (by positivity) (by positivity)
    exact mul_le_mul h1 hpow (by positivity) (by positivity)
  have hkk : ((k : ℝ) + 1) ≤ (k : ℝ) + 2 := by linarith
  have hkk2 : ((k : ℝ) + 1) * ((k : ℝ) + 1)
      ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    apply mul_le_mul_of_nonneg_left hkk (by positivity)
  have hrpow : r ^ (k - 1) ≤ r ^ k / r := by
    match k with
    | 0 =>
      simp only [Nat.zero_sub, pow_zero]
      have hrle : r ≤ 1 := le_of_lt hr1
      have h1r : (1:ℝ) ≤ 1 / r := by
        rw [le_div_iff₀ hr0]
        simp [hrle]
      simpa using h1r
    | (j + 1) =>
      have hsub : (j + 1 - 1) = j := by omega
      rw [hsub]
      have hpow : r ^ (j + 1) = r ^ j * r := pow_succ r j
      rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hr0)]
  have h2 : (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1)
      ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by
    have hA : (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1)
        ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      have := mul_le_mul_of_nonneg_left hkk2 (show (0:ℝ) ≤ 2 by norm_num)
      linarith [this]
    have hB : (0:ℝ) ≤ r ^ (k - 1) := pow_nonneg hr0.le _
    have hC : (0:ℝ) ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      positivity
    calc (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1)
        ≤ (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) * r ^ (k - 1) :=
          mul_le_mul_of_nonneg_right hA hB
      _ ≤ (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) * (r ^ k / r) :=
          mul_le_mul_of_nonneg_left hrpow hC
      _ = 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by ring
  rw [norm_mul, norm_mul, norm_pow]
  linarith [hmain, h2]

theorem S32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt S32 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * y ^ (k - 1)) y := by
  have hrN : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hbase := summable_succ_mul_succ_pow32 (r := r) hrN
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r)) := by
    have heq : (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r))
        = fun k : ℕ => (2 / r)
          * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k) := by
      funext k
      field_simp
    rw [heq]
    exact hbase.mul_left (2 / r)
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun w : ℝ => aCoeff32 k * w ^ k)
        (aCoeff32 k * (k : ℝ) * z ^ (k - 1)) z :=
    fun k z _ => S32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff32 k * (k : ℝ) * z ^ (k - 1)‖
        ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) :=
    fun k z hz => S32_majorant hr0 hr1 k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun k : ℕ => aCoeff32 k * (0 : ℝ) ^ k) := by
    have h0 : ‖(0 : ℝ)‖ < 1 := by norm_num
    exact summable_S32_of_norm_lt_one h0
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 hsum0 hy
  have efun : (fun z : ℝ => ∑' k : ℕ, aCoeff32 k * z ^ k) = S32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

theorem F32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt
      (fun s : ℝ => bCoeff32 k * s ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
      (aCoeff32 k * y ^ (2 * k)) y := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * k + 1))
      ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) y := by
    have h := hasDerivAt_pow (2 * k + 1) y
    have heq : (2 * k + 1) - 1 = 2 * k := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (bCoeff32 k)
  have hD : ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := by positivity
  have hdiv := hmul.div_const ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
  have hsimp : bCoeff32 k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k))
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
      = aCoeff32 k * y ^ (2 * k) := by
    unfold aCoeff32
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

theorem F32_majorant {r : ℝ}
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff32 k * y ^ (2 * k)‖ ≤ 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  have hpow : ‖y‖ ^ (2 * k) ≤ (r ^ 2) ^ k := by
    have h2 : ‖y‖ ^ (2 * k) = (‖y‖ ^ 2) ^ k := by
      rw [← pow_mul]
    have hle : ‖y‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) 2
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) hle _
  rw [norm_mul, norm_pow]
  calc ‖aCoeff32 k‖ * ‖y‖ ^ (2 * k)
      ≤ (2 * ((k : ℝ) + 1)) * (r ^ 2) ^ k :=
        mul_le_mul ha hpow (by positivity) (by positivity)
    _ = 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by ring

theorem F32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt F32 (∑' k : ℕ, aCoeff32 k * y ^ (2 * k)) y := by
  have hr2 : ‖(r ^ 2 : ℝ)‖ < 1 := by
    have hnn : (0:ℝ) ≤ r ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hr0, hr1]
  have hbase := summable_succ_mul_pow32 (r := r ^ 2) hr2
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k)) :=
    hbase.mul_left 2
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt
        (fun s : ℝ => bCoeff32 k * s ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        (aCoeff32 k * z ^ (2 * k)) z :=
    fun k z _ => F32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff32 k * z ^ (2 * k)‖
        ≤ 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) :=
    fun k z hz => F32_majorant k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 summable_F32_zero hy
  have efun : (fun s : ℝ => ∑' k : ℕ, bCoeff32 k * s ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = F32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

theorem G32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
      ((-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)) y := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ (2 * k + 1))
      ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) y := by
    have h := hasDerivAt_pow (2 * k + 1) y
    have heq : (2 * k + 1) - 1 = 2 * k := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul ((-1 : ℝ) ^ k)
  have hdiv := hmul.div_const ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
  have hsimp : (-1 : ℝ) ^ k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k))
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
      = (-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ) := by
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

theorem G32_majorant {r : ℝ}
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖(-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)‖
      ≤ (r ^ 2) ^ k := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have hpow : ‖y‖ ^ (2 * k) ≤ (r ^ 2) ^ k := by
    have h2 : ‖y‖ ^ (2 * k) = (‖y‖ ^ 2) ^ k := by
      rw [← pow_mul]
    have hle : ‖y‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) 2
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) hle _
  have hD : (1:ℝ) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
    have hle : 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast hle
  simp only [norm_div, norm_mul, norm_pow]
  have h1 : ‖(-1 : ℝ)‖ ^ k = 1 := by simp
  have hDnn : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = (((2 * k + 1 : ℕ)) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1, hDnn, one_mul]
  calc ‖y‖ ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)
      ≤ (r ^ 2) ^ k / (((2 * k + 1 : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (r ^ 2) ^ k / 1 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hD
    _ = (r ^ 2) ^ k := by ring

theorem G32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt G32
      (∑' k : ℕ, (-1 : ℝ) ^ k * y ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) y := by
  have hr2 : ‖(r ^ 2 : ℝ)‖ < 1 := by
    have hnn : (0:ℝ) ≤ r ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hr0, hr1]
  have hu : Summable (fun k : ℕ => (r ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one hr2
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt
        (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        ((-1 : ℝ) ^ k * z ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)) z :=
    fun k z _ => G32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖(-1 : ℝ) ^ k * z ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)‖
        ≤ (r ^ 2) ^ k :=
    fun k z hz => G32_majorant k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 summable_G32_zero hy
  have efun : (fun t : ℝ => ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = G32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
