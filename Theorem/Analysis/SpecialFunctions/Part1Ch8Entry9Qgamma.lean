/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch8Entry9Qgamma
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry9Qgamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

/-- The wishlist digamma is the canonical `Complex.digamma`. -/
theorem chapter8Digamma_eq_digamma (z : ℂ) :
    chapter8Digamma z = Complex.digamma z := by
  unfold chapter8Digamma
  rw [Complex.digamma_def, logDeriv_apply]

/-- On `(0, ∞)` the unit power is the standard `Complex.cpow`. -/
theorem chapter8UnitPow_eq_cpow (x : ℂ) (u : ℝ) (hu : 0 < u) :
    chapter8UnitPow x u = (u : ℂ) ^ x := by
  have hune : u ≠ 0 := ne_of_gt hu
  have hcu : (u : ℂ) ≠ 0 := by exact_mod_cast hune
  unfold chapter8UnitPow
  simp only [hune, ↓reduceIte]
  rw [Complex.cpow_def_of_ne_zero hcu, Complex.ofReal_log hu.le]
  congr 1
  ring

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8. -/
theorem entry9_x_ne_zero {x : ℂ} (hx : 0 < x.re) : x ≠ 0 := by
  intro h
  rw [h] at hx
  simp at hx

theorem entry9_norm_unitPow_of_pos {x : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖chapter8UnitPow x u‖ = u ^ x.re := by
  have hre : (x * ((Real.log u : ℝ) : ℂ)).re = x.re * Real.log u := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  unfold chapter8UnitPow
  rw [ite_eq_right (ne_of_gt hu)]
  rw [Complex.norm_exp, Real.rpow_def_of_pos hu, hre]
  exact congrArg Real.exp (mul_comm _ _)

theorem entry9_one_add_unitPow_ne {x : ℂ} (hx : 0 < x.re) {u : ℝ} (hu : 0 < u) :
    1 + chapter8UnitPow x u ≠ 0 := by
  by_cases hu1 : u = 1
  · subst hu1
    unfold chapter8UnitPow
    rw [ite_eq_right one_ne_zero, Real.log_one]
    simp
  · intro hcon
    have hw1 : ‖chapter8UnitPow x u‖ = 1 := by
      have h1 : (1 : ℂ) = -chapter8UnitPow x u := eq_neg_of_add_eq_zero_left hcon
      have h2 := congrArg Norm.norm h1
      rw [norm_one, norm_neg] at h2
      exact h2.symm
    rw [entry9_norm_unitPow_of_pos hu] at hw1
    rcases lt_trichotomy u 1 with hlt | heq | hgt
    · have hlt1 := Real.rpow_lt_one hu.le hlt hx
      rw [hw1] at hlt1
      exact lt_irrefl 1 hlt1
    · exact hu1 heq
    · have hgt1 := Real.one_lt_rpow hgt hx
      rw [hw1] at hgt1
      exact lt_irrefl 1 hgt1

theorem entry9_one_add_unitPow_ne_Icc {x : ℂ} (hx : 0 < x.re) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) : 1 + chapter8UnitPow x u ≠ 0 := by
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    unfold chapter8UnitPow
    rw [ite_eq_left rfl]
    simp
  · exact entry9_one_add_unitPow_ne hx hpos

theorem entry9_continuousOn_unitPow_Ioi {x : ℂ} :
    ContinuousOn (chapter8UnitPow x) (Set.Ioi 0) := by
  have hlog : ContinuousOn (fun u : ℝ => ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun u hu => ne_of_gt (Set.mem_Ioi.mp hu))
  have hmul : ContinuousOn (fun u : ℝ => x * ((Real.log u : ℝ) : ℂ)) (Set.Ioi 0) :=
    ContinuousOn.const_mul hlog x
  have hexp : ContinuousOn (fun u : ℝ => Complex.exp (x * ((Real.log u : ℝ) : ℂ)))
      (Set.Ioi 0) :=
    Complex.continuous_exp.comp_continuousOn hmul
  refine hexp.congr ?_
  intro u hu
  unfold chapter8UnitPow
  rw [ite_eq_right (ne_of_gt (Set.mem_Ioi.mp hu))]

theorem entry9_continuousOn_ratio_Ioi {x : ℂ} (hx : 0 < x.re) :
    ContinuousOn (chapter8UnitPowRatio x) (Set.Ioi 0) := by
  have hN := entry9_continuousOn_unitPow_Ioi (x := x)
  have hD : ContinuousOn (fun u : ℝ => (1 : ℂ) + chapter8UnitPow x u) (Set.Ioi 0) :=
    continuousOn_const.add hN
  have hDen : ∀ u ∈ Set.Ioi (0 : ℝ), (1 : ℂ) + chapter8UnitPow x u ≠ 0 := by
    intro u hu
    exact entry9_one_add_unitPow_ne hx (Set.mem_Ioi.mp hu)
  have hdiv := ContinuousOn.div hN hD hDen
  refine hdiv.congr ?_
  intro u hu
  unfold chapter8UnitPowRatio
  rfl

theorem entry9_tendsto_unitPow_nhdsWithin {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (chapter8UnitPow x) (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds 0) := by
  have hxne : x.re ≠ 0 := ne_of_gt hx
  have hbound : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → ‖chapter8UnitPow x u‖ = u ^ x.re := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      unfold chapter8UnitPow
      rw [ite_eq_left rfl, norm_zero, Real.zero_rpow hxne]
    · exact entry9_norm_unitPow_of_pos hpos
  have hT : Filter.Tendsto (fun u : ℝ => u ^ x.re) (nhds (0 : ℝ)) (nhds ((0 : ℝ) ^ x.re)) :=
    Real.continuousAt_rpow_const 0 x.re (Or.inr hx.le)
  have h0 : (0 : ℝ) ^ x.re = 0 := Real.zero_rpow hxne
  rw [h0] at hT
  have hglim : Filter.Tendsto (fun u : ℝ => u ^ x.re)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds 0) :=
    hT.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hglim
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Icc 0 1)] with u hu
  rw [hbound u hu]

theorem entry9_ratio_at_zero {x : ℂ} : chapter8UnitPowRatio x 0 = 0 := by
  unfold chapter8UnitPowRatio chapter8UnitPow
  simp

theorem entry9_tendsto_ratio_nhdsWithin {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (chapter8UnitPowRatio x) (nhdsWithin (0 : ℝ) (Set.Icc 0 1))
      (nhds (chapter8UnitPowRatio x 0)) := by
  rw [entry9_ratio_at_zero]
  have hN := entry9_tendsto_unitPow_nhdsWithin hx
  have hD : Filter.Tendsto (fun u : ℝ => (1 : ℂ) + chapter8UnitPow x u)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 1)) (nhds ((1 : ℂ) + 0)) :=
    tendsto_const_nhds.add hN
  have hne : ((1 : ℂ) + 0) ≠ 0 := by norm_num
  have hdiv := Filter.Tendsto.div hN hD hne
  have h0 : (0 : ℂ) / ((1 : ℂ) + 0) = 0 := by norm_num
  rw [h0] at hdiv
  exact hdiv.congr (fun u => rfl)

theorem entry9_continuousOn_ratio_Icc {x : ℂ} (hx : 0 < x.re) :
    ContinuousOn (chapter8UnitPowRatio x) (Set.Icc 0 1) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    exact entry9_tendsto_ratio_nhdsWithin hx
  · have huIoi : u ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hpos
    have hAt : ContinuousAt (chapter8UnitPowRatio x) u :=
      (entry9_continuousOn_ratio_Ioi hx).continuousAt (isOpen_Ioi.mem_nhds huIoi)
    exact hAt.continuousWithinAt

theorem entry9_intervalIntegrable {x : ℂ} (hx : 0 < x.re) :
    IntervalIntegrable (chapter8UnitPowRatio x) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (entry9_continuousOn_ratio_Icc hx)

theorem entry9_re_inv_pos {x : ℂ} (hx : 0 < x.re) : 0 < (1 / x).re := by
  have hxne := entry9_x_ne_zero hx
  rw [one_div, Complex.inv_re]
  exact div_pos hx (Complex.normSq_pos.mpr hxne)

theorem entry9_re_inv_two_mul_pos {x : ℂ} (hx : 0 < x.re) : 0 < (1 / (2 * x)).re := by
  have hxne := entry9_x_ne_zero hx
  have h2x : (2 * x).re = 2 * x.re := by simp [Complex.mul_re]
  rw [one_div, Complex.inv_re, h2x]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) hxne))

theorem entry9_gamma_ne_one_div_two_mul_add {x : ℂ} (hx : 0 < x.re) :
    Complex.Gamma (1 / (2 * x) + 1) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.one_re]
  have h := entry9_re_inv_two_mul_pos hx
  linarith

theorem entry9_gamma_ne_one_div_add {x : ℂ} (hx : 0 < x.re) :
    Complex.Gamma (1 / x + 1) ≠ 0 := by
  apply Complex.Gamma_ne_zero_of_re_pos
  rw [Complex.add_re, Complex.one_re]
  have h := entry9_re_inv_pos hx
  linarith

theorem entry9_two_mul_lhs {x : ℂ} (hx : 0 < x.re) :
    2 * (1 / (2 * x) + 1 / 2) = 1 / x + 1 := by
  have hxne := entry9_x_ne_zero hx
  field_simp

theorem entry9_two_mul_rhs (x : ℂ) :
    1 / (2 * x) + 1 / 2 + 1 / 2 = 1 / (2 * x) + 1 := by
  ring

theorem entry9_two_mul_side {x : ℂ} (hx : 0 < x.re) :
    ∀ m : ℕ, 2 * (1 / (2 * x) + 1 / 2) ≠ -((m : ℕ) : ℂ) := by
  intro m hm
  have h2s := entry9_two_mul_lhs hx
  rw [h2s] at hm
  have hpos : (0 : ℝ) < (1 / x + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    have h := entry9_re_inv_pos hx
    linarith
  have hre := congrArg Complex.re hm
  rw [Complex.neg_re, Complex.natCast_re] at hre
  have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
  linarith

theorem entry9_unitPow_add {x y : ℂ} {u : ℝ} (hu : u ≠ 0) :
    chapter8UnitPow (x + y) u = chapter8UnitPow x u * chapter8UnitPow y u := by
  unfold chapter8UnitPow
  rw [ite_eq_right hu, ite_eq_right hu, ite_eq_right hu, add_mul, Complex.exp_add]

theorem entry9_unitPow_nat_mul {x : ℂ} {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    chapter8UnitPow ((k : ℂ) * x) u = (chapter8UnitPow x u) ^ k := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    unfold chapter8UnitPow
    rw [ite_eq_right hu, zero_mul, Complex.exp_zero]
  | succ n ih =>
    have hcast : ((((n + 1 : ℕ)) : ℂ) * x) = (n : ℂ) * x + x := by push_cast; ring
    rw [hcast, entry9_unitPow_add hu, ih, pow_succ]

theorem entry9_unitPow_succ_mul {x : ℂ} {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    chapter8UnitPow (((k : ℂ) + 1) * x) u = (chapter8UnitPow x u) ^ (k + 1) := by
  have hcast : (((k : ℂ) + 1) * x) = x + (k : ℂ) * x := by ring
  rw [hcast, entry9_unitPow_add hu, entry9_unitPow_nat_mul hu, pow_succ']

theorem entry9_geom_summand {x : ℂ} {u : ℝ} (k : ℕ) :
    (-chapter8UnitPow x u) ^ k * chapter8UnitPow x u =
      (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u := by
  by_cases hu : u = 0
  · subst hu
    have h0 : ∀ w : ℂ, chapter8UnitPow w 0 = 0 := by
      intro w
      unfold chapter8UnitPow
      simp
    rw [h0, h0]
    simp
  · rw [entry9_unitPow_succ_mul hu k, neg_pow, pow_succ]
    ring

theorem entry9_geom_partial {x : ℂ} (hx : 0 < x.re) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (N : ℕ) :
    chapter8UnitPowRatio x u
      = (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u)
        + (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) u / (1 + chapter8UnitPow x u) := by
  have h1z : (1 : ℂ) + chapter8UnitPow x u ≠ 0 := entry9_one_add_unitPow_ne_Icc hx hu
  have hgeom := geom_sum_mul (-chapter8UnitPow x u) N
  have hsum : (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) u)
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [entry9_geom_summand]
  have hS : (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * (1 + chapter8UnitPow x u)
      = 1 - (-chapter8UnitPow x u) ^ N := by
    linear_combination -hgeom
  have key : chapter8UnitPow x u
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
          * (1 + chapter8UnitPow x u)
        + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u := by
    linear_combination (-chapter8UnitPow x u) * hS
  have hdiv : chapter8UnitPow x u / (1 + chapter8UnitPow x u)
      = (∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
        + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u / (1 + chapter8UnitPow x u) := by
    have hdiv2 : chapter8UnitPow x u / (1 + chapter8UnitPow x u)
        = ((∑ k ∈ range N, (-chapter8UnitPow x u) ^ k) * chapter8UnitPow x u
          * (1 + chapter8UnitPow x u)
          + (-chapter8UnitPow x u) ^ N * chapter8UnitPow x u) / (1 + chapter8UnitPow x u) := by
      exact congrArg (· / (1 + chapter8UnitPow x u)) key
    rw [hdiv2, add_div, mul_div_cancel_right₀ _ h1z]
  unfold chapter8UnitPowRatio
  rw [hsum, hdiv, entry9_geom_summand N]

theorem entry9_re_succ_mul_pos {x : ℂ} (hx : 0 < x.re) (k : ℕ) :
    0 < ((((k : ℂ) + 1) * x)).re := by
  have h1 : ((((k : ℂ) + 1) * x)) = (((((k : ℝ) + 1 : ℝ)) : ℂ) * x) := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
  rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) hx

theorem entry9_ofReal_log_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (((u⁻¹ : ℝ)) : ℂ) u := by
  have h1 : HasFDerivAt Real.log (ContinuousLinearMap.toSpanSingleton ℝ (u⁻¹ : ℝ)) u :=
    (Real.hasDerivAt_log (ne_of_gt hu)).hasFDerivAt
  have h2 : HasFDerivAt (⇑Complex.ofRealCLM) Complex.ofRealCLM (Real.log u) :=
    Complex.ofRealCLM.hasFDerivAt
  have h3 := HasFDerivAt.comp u h2 h1
  have h4 := h3.hasDerivAt
  have hder : (Complex.ofRealCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ (u⁻¹ : ℝ)) 1
      = (((u⁻¹ : ℝ)) : ℂ) := by simp
  rw [hder] at h4
  exact h4.congr_of_eventuallyEq (Eventually.of_forall fun v => rfl)

theorem entry9_hasDerivAt_unitPow_succ {y : ℂ} (hy : 0 < y.re) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1))
      (chapter8UnitPow y u) u := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hy1 : y + 1 ≠ 0 := by
    intro hcon
    have hre : y.re + 1 = 0 := by
      have h := congrArg Complex.re hcon
      simpa using h
    linarith
  have hlog := entry9_ofReal_log_hasDerivAt hu
  have hmul : HasDerivAt (fun v : ℝ => (y + 1) * ((Real.log v : ℝ) : ℂ))
      ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) u :=
    hlog.const_mul (y + 1)
  have hexp : HasDerivAt (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)))
      (Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ))) u :=
    HasDerivAt.cexp hmul
  have hdiv : HasDerivAt
      (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)) / (y + 1))
      (Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) *
        ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)) u :=
    hexp.div_const (y + 1)
  have hexp_log : Complex.exp (((Real.log u : ℝ)) : ℂ) = ((u : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hu]
  have hder : Complex.exp ((y + 1) * ((Real.log u : ℝ) : ℂ)) *
        ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
      = chapter8UnitPow y u := by
    have e1 : ((y + 1 : ℂ)) * (((Real.log u : ℝ)) : ℂ)
        = y * (((Real.log u : ℝ)) : ℂ) + (((Real.log u : ℝ)) : ℂ) := by ring
    have huc : (((u : ℝ)) : ℂ) * (((u⁻¹ : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hu0, Complex.ofReal_one]
    have hcancel : ((y + 1 : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) / (y + 1) = (((u⁻¹ : ℝ)) : ℂ) := by
      rw [div_eq_iff hy1]
      ring
    have step1 : Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
          * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
        = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) := by
      calc Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
              * ((y + 1) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)
          = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ))
              * ((((y + 1)) * (((u⁻¹ : ℝ)) : ℂ)) / (y + 1)) := by ring
        _ = Complex.exp ((y + 1) * (((Real.log u : ℝ)) : ℂ)) * (((u⁻¹ : ℝ)) : ℂ) := by
          rw [hcancel]
    rw [step1, e1, Complex.exp_add, hexp_log, mul_assoc, huc, mul_one]
    unfold chapter8UnitPow
    rw [ite_eq_right hu0]
  have hdiv2 : HasDerivAt (fun v : ℝ => Complex.exp ((y + 1) * ((Real.log v : ℝ) : ℂ)) / (y + 1))
      (chapter8UnitPow y u) u :=
    hder ▸ hdiv
  have hdiv3 : HasDerivAt (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1))
      (chapter8UnitPow y u) u := by
    apply hdiv2.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hu0] with v hv
    unfold chapter8UnitPow
    rw [ite_eq_right hv]
  exact hdiv3

theorem entry9_continuousOn_unitPow_Icc {y : ℂ} (hy : 0 < y.re) :
    ContinuousOn (chapter8UnitPow y) (Set.Icc 0 1) := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with h0 | hpos
  · subst h0
    have h0v : chapter8UnitPow y 0 = 0 := by
      unfold chapter8UnitPow
      simp
    unfold ContinuousWithinAt
    rw [h0v]
    exact entry9_tendsto_unitPow_nhdsWithin hy
  · have huIoi : u ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr hpos
    have hAt : ContinuousAt (chapter8UnitPow y) u :=
      (entry9_continuousOn_unitPow_Ioi (x := y)).continuousAt (isOpen_Ioi.mem_nhds huIoi)
    exact hAt.continuousWithinAt

theorem entry9_integral_unitPow {y : ℂ} (hy : 0 < y.re) :
    ∫ v in (0 : ℝ)..1, chapter8UnitPow y v = 1 / (y + 1) := by
  have hy1 : y + 1 ≠ 0 := by
    intro hcon
    have hre : y.re + 1 = 0 := by
      have h := congrArg Complex.re hcon
      simpa using h
    linarith
  have hy1re : 0 < (y + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hF : ContinuousOn (fun v : ℝ => chapter8UnitPow (y + 1) v / (y + 1)) (Set.Icc 0 1) :=
    (entry9_continuousOn_unitPow_Icc hy1re).div_const _
  have hint : IntervalIntegrable (chapter8UnitPow y) volume 0 1 :=
    (entry9_continuousOn_unitPow_Icc hy).intervalIntegrable_of_Icc (by norm_num)
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun w : ℝ => chapter8UnitPow (y + 1) w / (y + 1)) (chapter8UnitPow y v) v := by
    intro v hv
    exact entry9_hasDerivAt_unitPow_succ hy (Set.mem_Ioo.mp hv).1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hF hderiv hint
  have hF1 : chapter8UnitPow (y + 1) 1 / (y + 1) = 1 / (y + 1) := by
    unfold chapter8UnitPow
    rw [ite_eq_right one_ne_zero, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hF0 : chapter8UnitPow (y + 1) 0 / (y + 1) = 0 := by
    unfold chapter8UnitPow
    rw [ite_eq_left rfl, zero_div]
  rw [hF1, hF0, sub_zero] at hftc
  exact hftc

theorem entry9_integrableOn_remainder_Ioc {x : ℂ} (hx : 0 < x.re) (N : ℕ) :
    MeasureTheory.IntegrableOn
      (fun v => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Ioc 0 1) volume := by
  have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v)
      (Set.Icc 0 1) :=
    continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx N))
  have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
    continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
  have hdiv : ContinuousOn
      (fun v : ℝ => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Icc 0 1) :=
    hnum.div hden (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
  exact hdiv.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem entry9_partial_integral {x : ℂ} (hx : 0 < x.re) (N : ℕ) :
    ∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v
      = (∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
        + ∫ v in (0 : ℝ)..1,
            ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hEq : Set.EqOn (chapter8UnitPowRatio x)
      (fun v => (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
        + ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      (Set.Ioc 0 1) := by
    intro v hv
    exact entry9_geom_partial hx ⟨le_of_lt hv.1, hv.2⟩ N
  have hsum_on : ∀ k ∈ range N, MeasureTheory.IntegrableOn
      (fun v => (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v) (Set.Ioc 0 1) volume := by
    intro k _
    have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
        (Set.Icc 0 1) :=
      continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx k))
    exact hnum.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hRI : MeasureTheory.IntegrableOn
      (fun v => (-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (Set.Ioc 0 1) volume :=
    entry9_integrableOn_remainder_Ioc hx N
  have hsumI : MeasureTheory.Integrable
      (fun v => ∑ k ∈ range N, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
      (volume.restrict (Set.Ioc 0 1)) :=
    MeasureTheory.integrable_finsetSum _ (fun k hk => hsum_on k hk)
  have hterm : ∀ k ∈ range N,
      (∫ v in Set.Ioc (0 : ℝ) 1, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v ∂volume)
        = (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)) := by
    intro k _
    rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le h01,
      entry9_integral_unitPow (entry9_re_succ_mul_pos hx k)]
  have hval : (∫ v in Set.Ioc (0 : ℝ) 1,
        (∑ k ∈ range N, (-1 : ℂ) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v) ∂volume)
      = ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)) := by
    rw [MeasureTheory.integral_finsetSum _ (fun k hk => hsum_on k hk)]
    exact Finset.sum_congr rfl (fun k hk => hterm k hk)
  have e1 : (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)
      = ∫ v in Set.Ioc (0 : ℝ) 1, chapter8UnitPowRatio x v ∂volume :=
    intervalIntegral.integral_of_le h01
  have e2 : (∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      = ∫ v in Set.Ioc (0 : ℝ) 1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) ∂volume :=
    intervalIntegral.integral_of_le h01
  have haeEq : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Ioc (0 : ℝ) 1 →
      chapter8UnitPowRatio x v
        = (∑ k ∈ range N, (-1) ^ k * chapter8UnitPow (((k : ℂ) + 1) * x) v)
          + ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) :=
    Eventually.of_forall fun v hv => hEq hv
  have hcongr := MeasureTheory.setIntegral_congr_ae measurableSet_Ioc haeEq
  rw [e1, e2]
  exact (hcongr.trans (MeasureTheory.integral_add hsumI hRI)).trans (by rw [hval])

theorem entry9_tendsto_remainder_integral {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto
      (fun N : ℕ => ∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)))
      Filter.atTop (nhds 0) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h1c : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    have hset : {v : ℝ | ¬ v ≠ 1} = {1} := by
      ext v
      simp
    rw [hset]
    exact Real.volume_singleton
  have hAES : ∀ N : ℕ, AEStronglyMeasurable
      (fun v => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
      (volume.restrict (Set.Ioc 0 1)) := by
    intro N
    have hnum : ContinuousOn (fun v : ℝ => (-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v)
        (Set.Icc 0 1) :=
      continuousOn_const.mul (entry9_continuousOn_unitPow_Icc (entry9_re_succ_mul_pos hx N))
    have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
      continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
    have hdiv : ContinuousOn
        (fun v : ℝ => (-1 : ℂ) ^ N *
          chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
        (Set.Icc 0 1) :=
      hnum.div hden (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
    exact (hdiv.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hBint : MeasureTheory.Integrable (fun v : ℝ => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖)
      (volume.restrict (Set.Ioc 0 1)) := by
    have hden : ContinuousOn (fun v : ℝ => (1 : ℂ) + chapter8UnitPow x v) (Set.Icc 0 1) :=
      continuousOn_const.add (entry9_continuousOn_unitPow_Icc hx)
    have hBcont : ContinuousOn
        (fun v : ℝ => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖) (Set.Icc 0 1) := by
      have h1 := hden.inv₀ (fun v hv => entry9_one_add_unitPow_ne_Icc hx hv)
      have h2 := h1.norm
      simpa [Pi.inv_apply] using h2
    exact hBcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ N : ℕ, ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖(-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)‖
        ≤ ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖ := by
    intro N
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with v hv
    have hv_pos : 0 < v := (Set.mem_Ioc.mp hv).1
    have hv_le1 : v ≤ 1 := (Set.mem_Ioc.mp hv).2
    have hD : (1 : ℂ) + chapter8UnitPow x v ≠ 0 :=
      entry9_one_add_unitPow_ne_Icc hx ⟨le_of_lt hv_pos, hv_le1⟩
    have h1N : ‖(-1 : ℂ) ^ N‖ = 1 := by simp
    have hU1 : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ ≤ 1 := by
      have hnorm : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ = v ^ ((((N : ℝ) + 1) * x.re)) := by
        have hwre : ((((N : ℂ) + 1) * x)).re = (((N : ℝ) + 1) * x.re) := by
          have h1 : ((((N : ℂ) + 1) * x)) = (((((N : ℝ) + 1 : ℝ)) : ℂ) * x) := by
            rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
          rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [entry9_norm_unitPow_of_pos hv_pos, hwre]
      rw [hnorm]
      apply Real.rpow_le_one (le_of_lt hv_pos) hv_le1
      apply mul_nonneg _ hx.le
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    rw [norm_div, norm_mul, h1N, one_mul, norm_inv, div_eq_mul_inv]
    have hle : ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ * ‖(1 : ℂ) + chapter8UnitPow x v‖⁻¹
        ≤ 1 * ‖(1 : ℂ) + chapter8UnitPow x v‖⁻¹ :=
      mul_le_mul_of_nonneg_right hU1 (inv_nonneg.mpr (norm_nonneg _))
    rwa [one_mul] at hle
  have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      Filter.Tendsto
        (fun N : ℕ => (-1 : ℂ) ^ N *
          chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
        Filter.atTop (nhds 0) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1c] with v hv1 hvIoc
    have hv_pos : 0 < v := (Set.mem_Ioc.mp hvIoc).1
    have hv_le1 : v ≤ 1 := (Set.mem_Ioc.mp hvIoc).2
    have hv_lt1 : v < 1 := lt_of_le_of_ne hv_le1 hv1
    have hnorm : ∀ N : ℕ,
        ‖chapter8UnitPow (((N : ℂ) + 1) * x) v‖ = v ^ ((((N : ℝ) + 1) * x.re)) := by
      intro N
      have hwre : ((((N : ℂ) + 1) * x)).re = (((N : ℝ) + 1) * x.re) := by
        have h1 : ((((N : ℂ) + 1) * x)) = (((((N : ℝ) + 1 : ℝ)) : ℂ) * x) := by
          rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_natCast]
        rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [entry9_norm_unitPow_of_pos hv_pos, hwre]
    have hpow : Filter.Tendsto
        (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re))) Filter.atTop (nhds 0) := by
      have hvr : v ^ x.re < 1 := Real.rpow_lt_one (le_of_lt hv_pos) hv_lt1 hx
      have hvr0 : 0 ≤ v ^ x.re := Real.rpow_nonneg (le_of_lt hv_pos) _
      have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one hvr0 hvr
      have hshift : Filter.Tendsto (fun N : ℕ => (v ^ x.re) ^ (N + 1)) Filter.atTop (nhds 0) := by
        have hmul := hbase.const_mul (v ^ x.re)
        simpa [pow_succ'] using hmul
      have heq : (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re)))
          = (fun N : ℕ => (v ^ x.re) ^ (N + 1)) := by
        funext N
        have hcast : ((((N + 1 : ℕ)) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
        rw [← hcast, ← Real.rpow_natCast _ (N + 1), ← Real.rpow_mul (le_of_lt hv_pos)]
        congr 1
        ring
      rw [heq]
      exact hshift
    have hDbound : Filter.Tendsto
        (fun N : ℕ => v ^ ((((N : ℝ) + 1) * x.re)) / ‖(1 : ℂ) + chapter8UnitPow x v‖)
        Filter.atTop (nhds 0) := by
      have h2 := hpow.div_const (‖(1 : ℂ) + chapter8UnitPow x v‖)
      rwa [zero_div] at h2
    refine squeeze_zero_norm' (Eventually.of_forall fun N : ℕ => ?_) hDbound
    have h1N : ‖(-1 : ℂ) ^ N‖ = 1 := by simp
    have e : ‖(-1 : ℂ) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)‖
        = v ^ ((((N : ℝ) + 1) * x.re)) / ‖(1 : ℂ) + chapter8UnitPow x v‖ := by
      rw [norm_div, norm_mul, h1N, one_mul, hnorm N]
    exact le_of_eq e
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun N v => (-1 : ℂ) ^ N *
      chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v))
    (f := fun _ => 0)
    (fun v => ‖((1 : ℂ) + chapter8UnitPow x v)⁻¹‖)
    (μ := volume.restrict (Set.Ioc 0 1))
    hAES hBint hbound hae
  have hgoal : (fun N : ℕ => ∫ v in (0 : ℝ)..1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v /
          (1 + chapter8UnitPow x v)))
      = (fun N : ℕ => ∫ v in Set.Ioc (0 : ℝ) 1,
        ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v /
          (1 + chapter8UnitPow x v)) ∂volume) := by
    funext N
    exact intervalIntegral.integral_of_le h01
  rw [hgoal]
  simpa using hdct

theorem entry9_tendsto_partial {x : ℂ} (hx : 0 < x.re) :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
      Filter.atTop (nhds (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)) := by
  have hrem := entry9_tendsto_remainder_integral hx
  have heq : (fun N : ℕ => ∑ k ∈ range N, (-1) ^ k * (1 / ((((k : ℂ) + 1) * x) + 1)))
      = fun N : ℕ => (∫ v in (0 : ℝ)..1, chapter8UnitPowRatio x v)
        - ∫ v in (0 : ℝ)..1,
          ((-1) ^ N * chapter8UnitPow (((N : ℂ) + 1) * x) v / (1 + chapter8UnitPow x v)) := by
    funext N
    have h := entry9_partial_integral hx N
    rw [h]
    ring
  rw [heq]
  simpa using Filter.Tendsto.sub tendsto_const_nhds hrem

end
end Entry9Qgamma
end Ramanujan.Part1Ch8
end
