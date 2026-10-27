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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part6
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

theorem auxF_hasDerivAt {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxF ((x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀)) x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi / 2 := (Set.mem_Ioo.mp hx₀).2
  have hxIoo : x₀ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin x₀ := by
    have hlt : x₀ < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hx0_pos hlt
  have hsin_ne : Real.sin x₀ ≠ 0 := ne_of_gt hsin_pos
  have hsin_abs : |Real.sin x₀| < 1 := aux_sin_abs_lt_one hxIoo
  set c : ℝ := (x₀ + Real.pi / 2) / 2 with hcdef
  have hc0 : 0 < c := by linarith [Real.pi_pos]
  have hc1 : c < Real.pi / 2 := by unfold c; linarith
  have hxc : x₀ < c := by unfold c; linarith
  have hxmem : x₀ ∈ Set.Ioo 0 c := ⟨hx0_pos, hxc⟩
  have hsub : Set.Ioo 0 c ⊆ Set.Ioo (-c) c := by
    intro y hy
    have hy1 : 0 < y := (Set.mem_Ioo.mp hy).1
    have hy2 : y < c := (Set.mem_Ioo.mp hy).2
    constructor <;> linarith
  have hsin_b := aux_sin_c_bounds hc0 hc1
  set rho : ℝ := Real.sin c with hrhodef
  have hrho0 : 0 ≤ rho := hsin_b.1
  have hrho1 : rho < 1 := hsin_b.2
  have hu : Summable (fun k : ℕ => rho ^ (2 * k + 1)) :=
    aux_pow_odd_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo 0 c,
      HasDerivAt (fun y => chapter9Entry23FactorialTerm y k)
        (Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))))
        y := by
    intro k y _
    have efun : (fun y => chapter9Entry23FactorialTerm y k) =
        (fun y => auxA k * Real.sin y ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) :=
      funext (fun y => aux_factorial_eq y k)
    rw [efun]
    have hDne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hsub2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have hpow0 := (Real.hasDerivAt_sin y).pow (2 * k + 2)
    rw [hsub2] at hpow0
    have hmul := hpow0.const_mul (auxA k)
    have hdiv := hmul.div_const ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)
    have heq : (auxA k * ((((2 * k + 2 : ℕ)) : ℝ) * Real.sin y ^ (2 * k + 1) *
        Real.cos y)) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) =
        Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo 0 c,
      ‖Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))‖ ≤
        rho ^ (2 * k + 1) := by
    intro k y hy
    have hymem : y ∈ Set.Ioo (-c) c := hsub hy
    have hsin_le : |Real.sin y| ≤ rho := aux_sin_abs_le_sin_c hc0 hc1 hymem
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hcos : ‖Real.cos y‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have hpow_le : |Real.sin y| ^ (2 * k + 1) ≤ rho ^ (2 * k + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hsin_le _
    have hpos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ)) := by
      apply Nat.cast_pos.mpr
      omega
    have hle1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((2 * k + 2 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := le_of_lt hpos
    have hnormb : ‖((((2 * k + 2 : ℕ)) : ℝ))‖ = ((((2 * k + 2 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hpow : (‖Real.sin y ^ (2 * k + 1)‖) = |Real.sin y| ^ (2 * k + 1) := by
      rw [norm_pow, Real.norm_eq_abs]
    rw [norm_mul, norm_div, norm_mul, hnormb, hpow]
    have hnn_pow : (0 : ℝ) ≤ |Real.sin y| ^ (2 * k + 1) := by positivity
    have hmid : ‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
        ≤ rho ^ (2 * k + 1) := by
      have e : ‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
          = (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1)) *
            (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by ring
      rw [e]
      calc (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ)))
          ≤ (1 * rho ^ (2 * k + 1)) * 1 := by
            apply mul_le_mul _ hdiv (by positivity) (by positivity)
            exact mul_le_mul hA hpow_le (by positivity) (by positivity)
        _ = rho ^ (2 * k + 1) := by ring
    calc ‖Real.cos y‖ * (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))
        ≤ 1 * rho ^ (2 * k + 1) := mul_le_mul hcos hmid (by positivity) (by positivity)
      _ = rho ^ (2 * k + 1) := one_mul _
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo 0 c).isPreconnected hterm hbound hxmem
    (aux_factorial_summable x₀) hxmem
  have efun : (fun z => ∑' k : ℕ, chapter9Entry23FactorialTerm z k) = auxF := by
    funext z
    rfl
  rw [efun] at hmain
  have hS_summ : Summable
      (fun k : ℕ => auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
    have hboundS : Summable (fun k : ℕ => |Real.sin x₀| ^ (2 * k + 1)) := by
      have hr : |(|Real.sin x₀| ^ 2)| < 1 := by
        have hsq : |Real.sin x₀| ^ 2 < 1 := by nlinarith [hsin_abs, abs_nonneg (Real.sin x₀)]
        have hnn : (0 : ℝ) ≤ |Real.sin x₀| ^ 2 := by positivity
        rwa [abs_of_nonneg hnn]
      have hgeo : Summable (fun k : ℕ => (|Real.sin x₀| ^ 2) ^ k) :=
        summable_geometric_of_abs_lt_one hr
      have h := hgeo.mul_left |Real.sin x₀|
      have heq : (fun k : ℕ => |Real.sin x₀| * (|Real.sin x₀| ^ 2) ^ k) =
          (fun k : ℕ => |Real.sin x₀| ^ (2 * k + 1)) := by
        funext k
        have e1 : (|Real.sin x₀| ^ 2) ^ k = |Real.sin x₀| ^ (2 * k) := by
          rw [← pow_mul]
        rw [e1]
        calc |Real.sin x₀| * |Real.sin x₀| ^ (2 * k)
            = |Real.sin x₀| ^ (2 * k) * |Real.sin x₀| := by ring
          _ = |Real.sin x₀| ^ (2 * k + 1) := (pow_succ _ _).symm
      rwa [heq] at h
    apply Summable.of_norm_bounded hboundS
    intro k
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hpos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ)) := by
      apply Nat.cast_pos.mpr
      omega
    have hle1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((2 * k + 2 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := le_of_lt hpos
    have hnormb : ‖((((2 * k + 2 : ℕ)) : ℝ))‖ = ((((2 * k + 2 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hpow : (‖Real.sin x₀ ^ (2 * k + 1)‖) = |Real.sin x₀| ^ (2 * k + 1) := by
      rw [norm_pow, Real.norm_eq_abs]
    rw [norm_div, norm_mul, hnormb, hpow]
    have hnn_pow : (0 : ℝ) ≤ |Real.sin x₀| ^ (2 * k + 1) := by positivity
    calc ‖auxA k‖ * |Real.sin x₀| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
        = (‖auxA k‖ * |Real.sin x₀| ^ (2 * k + 1)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by
          ring
      _ ≤ (1 * |Real.sin x₀| ^ (2 * k + 1)) * 1 := by
          apply mul_le_mul _ hdiv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hA hnn_pow
      _ = |Real.sin x₀| ^ (2 * k + 1) := by ring
  have hH_eq : auxH x₀ = Real.sin x₀ *
      (∑' k : ℕ, auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
    have hcongr : (fun k : ℕ => auxH_term x₀ k) =
        (fun k : ℕ => Real.sin x₀ *
          (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) := by
      funext k
      unfold auxH_term
      have e : Real.sin x₀ ^ (2 * k + 2) =
          Real.sin x₀ * Real.sin x₀ ^ (2 * k + 1) := by
        have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
        calc Real.sin x₀ ^ (2 * k + 2) = Real.sin x₀ ^ ((2 * k + 1) + 1) := by rw [← h2]
          _ = Real.sin x₀ ^ (2 * k + 1) * Real.sin x₀ := pow_succ _ _
          _ = Real.sin x₀ * Real.sin x₀ ^ (2 * k + 1) := by ring
      rw [e]
      ring
    have htsum : (∑' k : ℕ, auxH_term x₀ k) =
        ∑' k : ℕ, Real.sin x₀ *
          (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      rw [hcongr]
    have hmul : (∑' k : ℕ, Real.sin x₀ *
        (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) =
        Real.sin x₀ * (∑' k : ℕ,
          auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      rw [tsum_mul_left]
    have hPeq : (∑' k : ℕ, auxH_term x₀ k) = auxH x₀ := rfl
    rw [hPeq] at htsum
    rw [htsum, hmul]
  have hHval : auxH x₀ = x₀ ^ 2 / 2 := auxH_eq hxIoo
  have hS_eq : (∑' k : ℕ,
      auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) =
      (x₀ ^ 2 / 2) / Real.sin x₀ := by
    rw [← hHval, hH_eq]
    field_simp
  have hF_eq : (∑' k : ℕ, Real.cos x₀ *
      (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) =
      (x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀) := by
    rw [tsum_mul_left, hS_eq]
    ring
  rw [hF_eq] at hmain
  exact hmain

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
