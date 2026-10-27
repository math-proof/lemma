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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part5
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

theorem auxH_summable {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Summable (auxH_term x) := by
  have hsin : |Real.sin x| < 1 := aux_sin_abs_lt_one hx
  have hr : |(|Real.sin x| ^ 2)| < 1 := by
    have hsq : |Real.sin x| ^ 2 < 1 := by nlinarith [hsin, abs_nonneg (Real.sin x)]
    have hnn : (0 : ℝ) ≤ |Real.sin x| ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (|Real.sin x| ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have hbound : Summable (fun k : ℕ => |Real.sin x| ^ (2 * k + 2)) := by
    have h := hgeo.mul_left (|Real.sin x| ^ 2)
    have heq : (fun k : ℕ => |Real.sin x| ^ 2 * (|Real.sin x| ^ 2) ^ k) =
        (fun k : ℕ => |Real.sin x| ^ (2 * k + 2)) := by
      funext k
      have e1 : (|Real.sin x| ^ 2) ^ k = |Real.sin x| ^ (2 * k) := by
        rw [← pow_mul]
      rw [e1]
      have e2 : (2 : ℕ) + 2 * k = 2 * k + 2 := by ring
      calc |Real.sin x| ^ 2 * |Real.sin x| ^ (2 * k)
          = |Real.sin x| ^ (2 + 2 * k) := by rw [← pow_add]
        _ = |Real.sin x| ^ (2 * k + 2) := by rw [e2]
    rwa [heq] at h
  apply Summable.of_norm_bounded hbound
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
  have hpow : (‖Real.sin x ^ (2 * k + 2)‖) = |Real.sin x| ^ (2 * k + 2) := by
    rw [norm_pow, Real.norm_eq_abs]
  unfold auxH_term
  rw [norm_div, norm_mul, hnormb, hpow]
  have hnn_pow : (0 : ℝ) ≤ |Real.sin x| ^ (2 * k + 2) := by positivity
  calc ‖auxA k‖ * |Real.sin x| ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ))
      = (‖auxA k‖ * |Real.sin x| ^ (2 * k + 2)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by
        ring
    _ ≤ (1 * |Real.sin x| ^ (2 * k + 2)) * 1 := by
        apply mul_le_mul _ hdiv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hA hnn_pow
    _ = |Real.sin x| ^ (2 * k + 2) := by ring

theorem aux_pow_odd_summable {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    Summable (fun k : ℕ => rho ^ (2 * k + 1)) := by
  have hr : |(rho ^ 2)| < 1 := by
    have hsq : rho ^ 2 < 1 := by nlinarith [h0, h1, sq_nonneg rho]
    have hnn : (0 : ℝ) ≤ rho ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (rho ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have h := hgeo.mul_left rho
  have heq : (fun k : ℕ => rho * (rho ^ 2) ^ k) =
      (fun k : ℕ => rho ^ (2 * k + 1)) := by
    funext k
    have e1 : (rho ^ 2) ^ k = rho ^ (2 * k) := by
      rw [← pow_mul]
    rw [e1]
    calc rho * rho ^ (2 * k) = rho ^ (2 * k) * rho := by ring
      _ = rho ^ (2 * k + 1) := (pow_succ rho _).symm
  rwa [heq] at h

theorem auxH_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt auxH x₀ x₀ := by
  have habs : |x₀| < Real.pi / 2 := abs_lt.mpr (Set.mem_Ioo.mp hx₀)
  set c : ℝ := (|x₀| + Real.pi / 2) / 2 with hcdef
  have hc0 : 0 < c := by
    have hnn : (0 : ℝ) ≤ |x₀| := abs_nonneg _
    have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    linarith
  have hc1 : c < Real.pi / 2 := by
    unfold c
    linarith
  have hxc : |x₀| < c := by
    unfold c
    linarith
  have hxmem : x₀ ∈ Set.Ioo (-c) c := Set.mem_Ioo.mpr (abs_lt.mp hxc)
  have hsin_b := aux_sin_c_bounds hc0 hc1
  set rho : ℝ := Real.sin c with hrhodef
  have hrho0 : 0 ≤ rho := hsin_b.1
  have hrho1 : rho < 1 := hsin_b.2
  have hu : Summable (fun k : ℕ => rho ^ (2 * k + 1)) :=
    aux_pow_odd_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-c) c,
      HasDerivAt (fun y => auxH_term y k)
        (Real.cos y * auxP_term (Real.sin y) k) y := by
    intro k y _
    unfold auxH_term auxP_term
    have hDne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have hpow0 := (Real.hasDerivAt_sin y).pow (2 * k + 2)
    rw [hsub] at hpow0
    have hmul := hpow0.const_mul (auxA k)
    have hdiv := hmul.div_const ((((2 * k + 2 : ℕ)) : ℝ))
    have heq : (auxA k * ((((2 * k + 2 : ℕ)) : ℝ) * Real.sin y ^ (2 * k + 1) *
        Real.cos y)) / ((((2 * k + 2 : ℕ)) : ℝ)) =
        Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1)) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-c) c,
      ‖Real.cos y * auxP_term (Real.sin y) k‖ ≤ rho ^ (2 * k + 1) := by
    intro k y hy
    have hsin_le : |Real.sin y| ≤ rho := aux_sin_abs_le_sin_c hc0 hc1 hy
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hcos : ‖Real.cos y‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have hpow_le : |Real.sin y| ^ (2 * k + 1) ≤ rho ^ (2 * k + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hsin_le _
    unfold auxP_term
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs]
    calc ‖Real.cos y‖ * (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1))
        ≤ 1 * (1 * rho ^ (2 * k + 1)) := by
          apply mul_le_mul hcos _ (by positivity) (by positivity)
          apply mul_le_mul hA hpow_le (by positivity) (by positivity)
      _ = rho ^ (2 * k + 1) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-c) c).isPreconnected hterm hbound hxmem
    (auxH_summable (by
      have hsub : Set.Ioo (-c) c ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : -c < y := (Set.mem_Ioo.mp hy).1
        have hy2 : y < c := (Set.mem_Ioo.mp hy).2
        constructor <;> linarith [Real.pi_pos]
      exact hsub hxmem)) hxmem
  have efun : (fun z => ∑' k : ℕ, auxH_term z k) = auxH := by
    funext z
    rfl
  rw [efun] at hmain
  have htsum : (∑' k : ℕ, Real.cos x₀ * auxP_term (Real.sin x₀) k) = x₀ := by
    rw [tsum_mul_left]
    have hPeq : (∑' k : ℕ, auxP_term (Real.sin x₀) k) = auxP (Real.sin x₀) := rfl
    rw [hPeq]
    have hK : Real.cos x₀ * auxP (Real.sin x₀) = x₀ := auxK_eq hx₀
    exact hK
  rw [htsum] at hmain
  exact hmain

theorem auxH_zero : auxH 0 = 0 := by
  unfold auxH
  have h0 : ∀ k : ℕ, auxH_term 0 k = 0 := by
    intro k
    unfold auxH_term
    have hne : 2 * k + 2 ≠ 0 := by omega
    rw [Real.sin_zero, zero_pow hne, mul_zero, zero_div]
  rw [tsum_congr h0]
  exact tsum_zero

theorem auxH_eq {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    auxH x = x ^ 2 / 2 := by
  have hsq : ∀ y : ℝ, HasDerivAt (fun y => y ^ 2 / 2) y y := by
    intro y
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      have h := hasDerivAt_pow 2 y
      simpa [pow_one] using h
    have hdiv := hpow.div_const 2
    have heq : (2 * y) / 2 = y := by ring
    rw [heq] at hdiv
    exact hdiv
  have hDderiv : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
    intro y hy
    have h := (auxH_hasDerivAt hy).sub (hsq y)
    simp only [sub_self] at h
    exact h
  have hDcont : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      ContinuousAt (fun y => auxH y - y ^ 2 / 2) y :=
    fun y hy => (hDderiv y hy).continuousAt
  have hD0 : (fun y => auxH y - y ^ 2 / 2) 0 = 0 := by
    simp [auxH_zero]
  by_cases hx0 : x = 0
  · subst hx0
    simp [auxH_zero]
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hIcc_sub : Set.Icc x 0 ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : x ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ 0 := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxH y - y ^ 2 / 2) (Set.Icc x 0) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo x 0,
          HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc x 0 :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxH y - y ^ 2 / 2) (fun _ => 0)
          hneg hcont hderiv
      have hD0' : auxH 0 - (0 : ℝ) ^ 2 / 2 = 0 := by simp [auxH_zero]
      rw [hD0', zero_sub (auxH x - x ^ 2 / 2)] at hc
      have hne : (0 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have h0 : (-(auxH x - x ^ 2 / 2)) / (0 - x) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : -(auxH x - x ^ 2 / 2) = 0 := h0.resolve_right hne
      have hDx : auxH x - x ^ 2 / 2 = 0 := neg_eq_zero.mp hnum
      exact sub_eq_zero.mp hDx
    · have hIcc_sub : Set.Icc 0 x ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : 0 ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ x := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxH y - y ^ 2 / 2) (Set.Icc 0 x) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo 0 x,
          HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc 0 x :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxH y - y ^ 2 / 2) (fun _ => 0)
          hpos hcont hderiv
      have hD0' : auxH 0 - (0 : ℝ) ^ 2 / 2 = 0 := by simp [auxH_zero]
      rw [hD0', sub_zero (auxH x - x ^ 2 / 2)] at hc
      have hne : (x : ℝ) - 0 ≠ 0 := ne_of_gt (by linarith)
      have h0 : (auxH x - x ^ 2 / 2) / (x - 0) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : auxH x - x ^ 2 / 2 = 0 := h0.resolve_right hne
      exact sub_eq_zero.mp hnum

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
