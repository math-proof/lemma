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
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem aux_zetaThree_summable : Summable chapter9ZetaThreeTerm := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) :=
    (summable_nat_add_iff 1).mpr h
  unfold chapter9ZetaThreeTerm
  exact h2

theorem aux_sineTwo_summable (x : ℝ) : Summable (chapter9SineFourierTwoTerm x) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded h2
  intro j
  change ‖chapter9SineFourierTwoTerm x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)
  change ‖Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div]
  have hsin : |Real.sin (2 * (((j + 1 : ℕ)) : ℝ) * x)| ≤ 1 := Real.abs_sin_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  rw [abs_of_pos hpos]
  gcongr

theorem aux_cosineThree_summable (x : ℝ) :
    Summable (chapter9CosineFourierThreeTerm x) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) :=
    (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded h2
  intro j
  change ‖chapter9CosineFourierThreeTerm x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  change ‖Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div]
  have hcos : |Real.cos (2 * (((j + 1 : ℕ)) : ℝ) * x)| ≤ 1 := Real.abs_cos_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  rw [abs_of_pos hpos]
  gcongr

theorem aux_coeff_le_one (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)) ≤ 1 := by
  have hnat : 4 ^ k * (k.factorial ^ 2) ≤ (2 * k + 1).factorial := by
    have h4 : 4 ^ k ≤ (2 * k + 1) * k.centralBinom :=
      Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
    rw [Nat.centralBinom_eq_two_mul_choose] at h4
    have hchoose : (2 * k).choose k * k.factorial * (k.factorial) = (2 * k).factorial := by
      have hle : k ≤ 2 * k := Nat.le_mul_of_pos_left k (by norm_num)
      have h := Nat.choose_mul_factorial_mul_factorial hle
      have hsub : 2 * k - k = k := by omega
      rwa [hsub] at h
    have hfact : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial := by
      have : 2 * k + 1 = (2 * k) + 1 := by omega
      rw [this, Nat.factorial_succ]
    have hmul : 4 ^ k * (k.factorial ^ 2)
        ≤ ((2 * k + 1) * (2 * k).choose k) * (k.factorial ^ 2) :=
      Nat.mul_le_mul_right _ h4
    rw [hfact]
    rw [← hchoose]
    have hrw : ((2 * k + 1) * (2 * k).choose k) * k.factorial ^ 2
        = (2 * k + 1) * ((2 * k).choose k * k.factorial * k.factorial) := by ring
    rwa [hrw] at hmul
  have h24 : (2 : ℝ) ^ (2 * k) = (4 : ℝ) ^ k := by
    have h : ((2 : ℝ) ^ 2) ^ k = (2 : ℝ) ^ (2 * k) := by rw [pow_mul]
    rw [← h]
    norm_num
  have hcast : (4 : ℝ) ^ k * ((k.factorial : ℝ) ^ 2) ≤ (((2 * k + 1).factorial : ℝ)) := by
    have hcast0 : (((4 ^ k * (k.factorial ^ 2) : ℕ)) : ℝ)
        ≤ ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_le.mpr hnat
    push_cast at hcast0
    exact hcast0
  rw [h24]
  have hpos : (0 : ℝ) < (((2 * k + 1).factorial : ℝ)) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_one hpos]
  exact hcast

theorem aux_factorial_summable (u : ℝ) : Summable (chapter9Entry23FactorialTerm u) := by
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded hbase
  intro k
  have hsin_le : |Real.sin u ^ (2 * k + 2)| ≤ 1 := by
    have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one _
    have h0 : 0 ≤ |Real.sin u| := abs_nonneg _
    calc |Real.sin u ^ (2 * k + 2)| = |Real.sin u| ^ (2 * k + 2) := by rw [abs_pow]
      _ ≤ 1 := pow_le_one₀ h0 h1
  have hden_pos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (by omega)
  have hfact_pos : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  change ‖chapter9Entry23FactorialTerm u k‖ ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)
  unfold chapter9Entry23FactorialTerm
  rw [Real.norm_eq_abs]
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by positivity
  have hkpos : (0 : ℝ) ≤ ((k.factorial : ℝ) ^ 2) := by positivity
  have hnum_abs : |(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin u ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * (((2 * k + 2 : ℕ)) : ℝ) ^ 2)|
      = ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg h2pos, abs_of_nonneg hkpos,
      abs_of_pos hfact_pos, abs_of_nonneg (le_of_lt hden_pos)]
    ring
  rw [hnum_abs]
  have hstep1 : |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2
      ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
    gcongr
  have hnn_sin_div : (0 : ℝ) ≤ |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 :=
    div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
  have hcoeff := aux_coeff_le_one k
  have hmid : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
      ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hcoeff hnn_sin_div
  have hstep2 : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
      ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
    calc _ ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := hmid
      _ = |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by ring
      _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep1
  have hstep3 : (1 : ℝ) / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have hle : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
        apply Nat.cast_le.mpr
        omega
      gcongr
  calc _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep2
    _ ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := hstep3

theorem aux_factorial_term_zero (k : ℕ) :
    chapter9Entry23FactorialTerm 0 k = 0 := by
  have h : (2 * k + 2 : ℕ) ≠ 0 := by omega
  change (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin 0 ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) = 0
  rw [Real.sin_zero, zero_pow h, mul_zero, zero_div]

theorem aux_factorial_tsum_zero :
    (∑' k : ℕ, chapter9Entry23FactorialTerm 0 k) = 0 := by
  simp [aux_factorial_term_zero]

theorem aux_cosine_term_zero (j : ℕ) :
    chapter9CosineFourierThreeTerm 0 j = chapter9ZetaThreeTerm j := by
  change Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * 0) / ((((j + 1 : ℕ)) : ℝ) ^ 3) =
    1 / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  simp

theorem aux_cosine_tsum_zero :
    (∑' j : ℕ, chapter9CosineFourierThreeTerm 0 j) = chapter9ZetaThree := by
  unfold chapter9ZetaThree
  have h : ∀ j : ℕ, chapter9CosineFourierThreeTerm 0 j = chapter9ZetaThreeTerm j :=
    aux_cosine_term_zero
  rw [tsum_congr h]

theorem aux_rhs_zero :
    chapter9Entry20LogTerm 0 +
        (0 : ℝ) / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm 0 j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm 0 j -
        chapter9ZetaThree / 4 = 0 := by
  have hlog : chapter9Entry20LogTerm 0 = 0 := by
    unfold chapter9Entry20LogTerm
    simp
  rw [hlog, aux_cosine_tsum_zero]
  ring

theorem aux_factorial_term_even (y : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm (-y) k = chapter9Entry23FactorialTerm y k := by
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  change (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin (-y) ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) =
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin y ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2))
  rw [Real.sin_neg, he.neg_pow (Real.sin y)]

theorem aux_factorial_tsum_even (y : ℝ) :
    (∑' k : ℕ, chapter9Entry23FactorialTerm (-y) k) =
      (∑' k : ℕ, chapter9Entry23FactorialTerm y k) :=
  tsum_congr (aux_factorial_term_even y)

theorem aux_sine_term_odd (y : ℝ) (j : ℕ) :
    chapter9SineFourierTwoTerm (-y) j = -chapter9SineFourierTwoTerm y j := by
  have harg : (2 : ℝ) * ((((j + 1 : ℕ)) : ℝ)) * (-y) =
      -(2 * ((((j + 1 : ℕ)) : ℝ)) * y) := by ring
  change Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * (-y)) / ((((j + 1 : ℕ)) : ℝ) ^ 2) =
    -(Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
  rw [harg, Real.sin_neg, neg_div]

theorem aux_cosine_term_even (y : ℝ) (j : ℕ) :
    chapter9CosineFourierThreeTerm (-y) j = chapter9CosineFourierThreeTerm y j := by
  have harg : (2 : ℝ) * ((((j + 1 : ℕ)) : ℝ)) * (-y) =
      -(2 * ((((j + 1 : ℕ)) : ℝ)) * y) := by ring
  change Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * (-y)) / ((((j + 1 : ℕ)) : ℝ) ^ 3) =
    Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  rw [harg, Real.cos_neg]

theorem aux_logterm_even (y : ℝ) :
    chapter9Entry20LogTerm (-y) = chapter9Entry20LogTerm y := by
  unfold chapter9Entry20LogTerm
  by_cases hy : y = 0
  · subst hy
    rw [neg_zero]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    have h1 : (-y) ^ 2 = y ^ 2 := by ring
    have h2 : |2 * Real.sin (-y)| = |2 * Real.sin y| := by
      rw [Real.sin_neg]
      have harg : (2 : ℝ) * (-Real.sin y) = -(2 * Real.sin y) := by ring
      rw [harg, abs_neg]
    simp only [hny, hy, ite_false, h1, h2]

theorem aux_rhs_even (y : ℝ) :
    chapter9Entry20LogTerm (-y) +
        (-y) / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm (-y) j -
        chapter9ZetaThree / 4 =
      chapter9Entry20LogTerm y +
        y / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm y j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm y j -
        chapter9ZetaThree / 4 := by
  have hA : (∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j) =
      -(∑' j : ℕ, chapter9SineFourierTwoTerm y j) := by
    have hcon : (∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j) =
        (∑' j : ℕ, -(chapter9SineFourierTwoTerm y j)) :=
      tsum_congr (aux_sine_term_odd y)
    rw [hcon, tsum_neg]
  have hB : (∑' j : ℕ, chapter9CosineFourierThreeTerm (-y) j) =
      (∑' j : ℕ, chapter9CosineFourierThreeTerm y j) :=
    tsum_congr (aux_cosine_term_even y)
  rw [aux_logterm_even y, hA, hB]
  ring

theorem aux_cosine_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => ∑' j : ℕ, chapter9CosineFourierThreeTerm y j)
      (-2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j) x := by
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h
  have hu : Summable (fun j : ℕ => 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h2 := hbase.mul_left 2
    simp only [mul_one_div] at h2
    exact h2
  have hterm : ∀ j : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => chapter9CosineFourierThreeTerm y j)
        (-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
          ((((j + 1 : ℕ)) : ℝ) ^ 3)) y := by
    intro j y
    change HasDerivAt
      (fun y => Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3))
      (-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3)) y
    have hlin : HasDerivAt (fun y : ℝ => 2 * ((((j + 1 : ℕ)) : ℝ)) * y)
        (2 * ((((j + 1 : ℕ)) : ℝ))) y := by
      have h := (hasDerivAt_id y).const_mul (2 * ((((j + 1 : ℕ)) : ℝ)))
      simpa using h
    exact (hlin.cos).div_const _
  have hbound : ∀ j : ℕ, ∀ y : ℝ,
      ‖-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    intro j y
    have hk : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hk2 : (0 : ℝ) < 2 * ((((j + 1 : ℕ)) : ℝ)) := mul_pos (by norm_num) hk
    have hden : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := pow_pos hk 3
    have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hnum : |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) *
        (2 * ((((j + 1 : ℕ)) : ℝ)))| ≤ 2 * ((((j + 1 : ℕ)) : ℝ)) := by
      rw [abs_mul, abs_neg, abs_of_pos hk2]
      calc |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| * (2 * ((((j + 1 : ℕ)) : ℝ)))
          ≤ 1 * (2 * ((((j + 1 : ℕ)) : ℝ))) :=
            mul_le_mul_of_nonneg_right hsin (le_of_lt hk2)
        _ = 2 * ((((j + 1 : ℕ)) : ℝ)) := one_mul _
    calc ‖-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
          ((((j + 1 : ℕ)) : ℝ) ^ 3)‖
        = |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))| /
          |((((j + 1 : ℕ)) : ℝ) ^ 3)| := by rw [Real.norm_eq_abs, abs_div]
      _ = |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))| /
          ((((j + 1 : ℕ)) : ℝ) ^ 3) := by rw [abs_of_pos hden]
      _ ≤ 2 * ((((j + 1 : ℕ)) : ℝ)) / ((((j + 1 : ℕ)) : ℝ) ^ 3) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
          have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hk
          field_simp
  have hmain := hasDerivAt_tsum hu hterm hbound (aux_cosineThree_summable x) x
  have hderiv : (∑' j : ℕ, -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) *
      (2 * ((((j + 1 : ℕ)) : ℝ))) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) =
      -2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    change -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3) =
      -2 * chapter9SineFourierTwoTerm x j
    change -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3) =
      -2 * (Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    have hk : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hk
    field_simp
  rw [hderiv] at hmain
  exact hmain

theorem aux_one_div_sq_summable :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr h

theorem aux_one_div_cube_summable :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr h

theorem aux_factorial_continuous :
    Continuous (fun u => ∑' k : ℕ, chapter9Entry23FactorialTerm u k) := by
  refine continuous_tsum ?_ aux_one_div_sq_summable ?_
  · intro k
    change Continuous (fun u => (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)))
    apply Continuous.div_const
    apply Continuous.mul
    · exact continuous_const
    · exact Real.continuous_sin.pow _
  · intro k u
    have hsin_le : |Real.sin u ^ (2 * k + 2)| ≤ 1 := by
      have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one _
      have h0 : 0 ≤ |Real.sin u| := abs_nonneg _
      calc |Real.sin u ^ (2 * k + 2)| = |Real.sin u| ^ (2 * k + 2) := by rw [abs_pow]
        _ ≤ 1 := pow_le_one₀ h0 h1
    have hden_pos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (by omega)
    have hfact_pos : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    change ‖chapter9Entry23FactorialTerm u k‖ ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)
    have hpoint : ‖chapter9Entry23FactorialTerm u k‖ ≤
        1 / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
      change ‖(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin u ^ (2 * k + 2) /
        ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2))‖ ≤ _
      have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by positivity
      have hkpos : (0 : ℝ) ≤ ((k.factorial : ℝ) ^ 2) := by positivity
      have hnum_abs : |(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
          Real.sin u ^ (2 * k + 2) /
          ((((2 * k + 1).factorial : ℝ)) * (((2 * k + 2 : ℕ)) : ℝ) ^ 2)|
          = ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
            (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
        rw [abs_div, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg h2pos, abs_of_nonneg hkpos,
          abs_of_pos hfact_pos, abs_of_nonneg (le_of_lt hden_pos)]
        ring
      rw [Real.norm_eq_abs, hnum_abs]
      have hstep1 : |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2
          ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
        gcongr
      have hnn_sin_div : (0 : ℝ) ≤
          |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 :=
        div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
      have hcoeff := aux_coeff_le_one k
      have hmid : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
          (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
          ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcoeff hnn_sin_div
      calc ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
          (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
          ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := hmid
        _ = |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by ring
        _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep1
    have hstep3 : (1 : ℝ) / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 ≤
        1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hle : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
          apply Nat.cast_le.mpr
          omega
        gcongr
    exact le_trans hpoint hstep3

theorem aux_sine_continuous :
    Continuous (fun y => ∑' j : ℕ, chapter9SineFourierTwoTerm y j) := by
  refine continuous_tsum ?_ aux_one_div_sq_summable ?_
  · intro j
    change Continuous (fun y =>
      Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    apply Continuous.div_const
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  · intro j y
    change ‖chapter9SineFourierTwoTerm y j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)
    change ‖Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_div]
    have hsin : |Real.sin (2 * (((j + 1 : ℕ)) : ℝ) * y)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    rw [abs_of_pos hpos]
    gcongr

theorem aux_cosine_continuous :
    Continuous (fun y => ∑' j : ℕ, chapter9CosineFourierThreeTerm y j) := by
  refine continuous_tsum ?_ aux_one_div_cube_summable ?_
  · intro j
    change Continuous (fun y =>
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3))
    apply Continuous.div_const
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  · intro j y
    change ‖chapter9CosineFourierThreeTerm y j‖ ≤
      (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
    change ‖Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ _
    rw [Real.norm_eq_abs, abs_div]
    have hcos : |Real.cos (2 * (((j + 1 : ℕ)) : ℝ) * y)| ≤ 1 :=
      Real.abs_cos_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    rw [abs_of_pos hpos]
    gcongr

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
