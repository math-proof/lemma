/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.Part1Ch9Entry1Logratio.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry1Logratio

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem entry1_hasDerivAt_mul (a s : ℝ) :
    HasDerivAt (fun t => a * t) a s := by
  have h := (hasDerivAt_id s).const_mul a
  simpa using h

theorem entry1_g_hasDerivAt (a s : ℝ) (hs : Real.sin s ≠ 0) :
    HasDerivAt (entry1_g a) (entry1_g' a s) s := by
  have hnum : HasDerivAt (fun t => Real.sin (a * t)) (Real.cos (a * s) * a) s :=
    (entry1_hasDerivAt_mul a s).sin
  have hden : HasDerivAt Real.sin (Real.cos s) s := Real.hasDerivAt_sin s
  have hdiv := hnum.div hden hs
  unfold entry1_g entry1_g'
  exact hdiv

theorem entry1_sin_ne_of_mem (δ B s : ℝ) (hδ : 0 < δ) (hB : B < Real.pi)
    (hs : s ∈ Set.Icc δ B) : Real.sin s ≠ 0 := by
  rw [Set.mem_Icc] at hs
  have hpos : 0 < s := lt_of_lt_of_le hδ hs.1
  have hlt : s < Real.pi := lt_of_le_of_lt hs.2 hB
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

theorem entry1_g_continuousOn (a δ B : ℝ) (hδ : 0 < δ) (hB : B < Real.pi) :
    ContinuousOn (entry1_g a) (Set.Icc δ B) := by
  intro s hs
  have hderiv := entry1_g_hasDerivAt a s (entry1_sin_ne_of_mem δ B s hδ hB hs)
  exact hderiv.continuousAt.continuousWithinAt

theorem entry1_g'_continuousOn (a δ B : ℝ) (hδ : 0 < δ) (hB : B < Real.pi) :
    ContinuousOn (entry1_g' a) (Set.Icc δ B) := by
  have hsin : ContinuousOn Real.sin (Set.Icc δ B) :=
    Real.continuous_sin.continuousOn
  have hcos : ContinuousOn Real.cos (Set.Icc δ B) :=
    Real.continuous_cos.continuousOn
  have hinner : Continuous (fun s : ℝ => a * s) :=
    continuous_const.mul continuous_id
  have hcos_a : ContinuousOn (fun s => Real.cos (a * s)) (Set.Icc δ B) :=
    (Real.continuous_cos.comp hinner).continuousOn
  have hsin_a : ContinuousOn (fun s => Real.sin (a * s)) (Set.Icc δ B) :=
    (Real.continuous_sin.comp hinner).continuousOn
  have hnum : ContinuousOn
      (fun s => Real.cos (a * s) * a * Real.sin s - Real.sin (a * s) * Real.cos s)
      (Set.Icc δ B) :=
    ((hcos_a.mul continuous_const.continuousOn).mul hsin).sub (hsin_a.mul hcos)
  have hden : ContinuousOn (fun s => Real.sin s ^ 2) (Set.Icc δ B) :=
    hsin.pow 2
  have h0 : ∀ s ∈ Set.Icc δ B, (Real.sin s ^ 2) ≠ 0 := by
    intro s hs
    exact pow_ne_zero 2 (entry1_sin_ne_of_mem δ B s hδ hB hs)
  have hdiv := hnum.div hden h0
  unfold entry1_g'
  exact hdiv

theorem entry1_g_bound_near_zero (a : ℝ) :
    ∃ δ₀ > 0, ∀ s : ℝ, 0 < s → s < δ₀ → |entry1_g a s| ≤ 2 * |a| := by
  have hcont : Tendsto Real.sinc (𝓝 0) (𝓝 1) := by
    have h := Real.continuous_sinc.tendsto 0
    rwa [Real.sinc_zero] at h
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), (1 / 2 : ℝ) ≤ Real.sinc y :=
    hcont.eventually (eventually_ge_nhds (by norm_num))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₀, hδ0, hball⟩ := hev
  refine ⟨δ₀, hδ0, fun s hs0 hsδ => ?_⟩
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hdist : dist s 0 < δ₀ := by
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hs0]
    exact hsδ
  have hsinc := hball hdist
  rw [Real.sinc_of_ne_zero hsne] at hsinc
  have hsin_pos : 0 < Real.sin s := by
    have hpos : (0 : ℝ) < Real.sin s / s := lt_of_lt_of_le (by norm_num) hsinc
    rcases div_pos_iff.mp hpos with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · linarith
  have hsin_ge : s / 2 ≤ Real.sin s := by
    have hle := (le_div_iff₀ hs0).mp hsinc
    linarith
  have hnum : |Real.sin (a * s)| ≤ |a| * s := by
    calc |Real.sin (a * s)| ≤ |a * s| := Real.abs_sin_le_abs
      _ = |a| * s := by rw [abs_mul, abs_of_pos hs0]
  unfold entry1_g
  rw [abs_div, abs_of_pos hsin_pos, div_le_iff₀ hsin_pos]
  nlinarith [hnum, hsin_ge, abs_nonneg a, hs0.le, hsin_pos.le]

theorem entry1_abs_sub_le (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have h := abs_add_le x (-y)
  rwa [← sub_eq_add_neg, abs_neg] at h

theorem entry1_integrand_tendsto_zero (a : ℝ) (N : ℕ) (B : ℝ) :
    Tendsto (fun s => (entry1_g a s) * Real.sin (2 * N * s))
      (𝓝[Set.Icc 0 B] 0) (𝓝 0) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀bound⟩ := entry1_g_bound_near_zero a
  have hball : ∀ᶠ s in 𝓝[Set.Icc 0 B] (0 : ℝ), s ∈ Metric.ball (0 : ℝ) δ₀ := by
    have hmem : Metric.ball (0 : ℝ) δ₀ ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ hδ₀pos
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Metric.ball (0 : ℝ) δ₀ :=
      eventually_of_mem hmem (fun s hs => hs)
    exact hev.filter_mono nhdsWithin_le_nhds
  have hIcc : ∀ᶠ s in 𝓝[Set.Icc 0 B] (0 : ℝ), s ∈ Set.Icc 0 B :=
    eventually_of_mem self_mem_nhdsWithin (fun s hs => hs)
  have hbound : ∀ᶠ s in 𝓝[Set.Icc 0 B] (0 : ℝ),
      ‖(entry1_g a s) * Real.sin (2 * N * s)‖ ≤
        ‖(2 * |a|) * Real.sin (2 * N * s)‖ := by
    filter_upwards [hball, hIcc] with s hsball hsIcc
    rw [Set.mem_Icc] at hsIcc
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hsball
    by_cases hs0 : s = 0
    · subst hs0
      simp [entry1_g]
    · have hspos : 0 < s := lt_of_le_of_ne hsIcc.1 (Ne.symm hs0)
      have hslt : s < δ₀ := by
        have hnorm : ‖s‖ < δ₀ := hsball
        rwa [Real.norm_eq_abs, abs_of_pos hspos] at hnorm
      have hg := hδ₀bound s hspos hslt
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
      have hpos2a : (0 : ℝ) ≤ 2 * |a| := by positivity
      rw [abs_of_nonneg hpos2a]
      exact mul_le_mul_of_nonneg_right hg (abs_nonneg _)
  have hlim : Tendsto (fun s => (2 * |a|) * Real.sin (2 * N * s))
      (𝓝[Set.Icc 0 B] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun s => (2 * |a|) * Real.sin (2 * N * s)) 0 :=
      (continuous_const.mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousAt
    have hval : (2 * |a|) * Real.sin (2 * (N : ℝ) * 0) = 0 := by simp
    have htend : Tendsto (fun s => (2 * |a|) * Real.sin (2 * N * s))
        (𝓝[Set.Icc 0 B] 0) (𝓝 ((2 * |a|) * Real.sin (2 * (N : ℝ) * 0))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rwa [hval] at htend
  have hnormlim : Tendsto (fun s => ‖(2 * |a|) * Real.sin (2 * N * s)‖)
      (𝓝[Set.Icc 0 B] 0) (𝓝 0) := by
    simpa using hlim.norm
  exact squeeze_zero_norm' hbound hnormlim

theorem entry1_near_zero_integral_bound (a : ℝ) (N : ℕ) (δ₀ : ℝ)
    (hδ₀bound : ∀ s : ℝ, 0 < s → s < δ₀ → |entry1_g a s| ≤ 2 * |a|)
    (u δ : ℝ) (hu0 : 0 ≤ u) (huδ : u ≤ δ) (hδ0 : δ < δ₀) :
    |∫ s in (0 : ℝ)..u, (entry1_g a s) * Real.sin (2 * N * s)| ≤
      (2 * |a|) * u := by
  have hpt : ∀ s ∈ Set.uIoc 0 u,
      ‖(entry1_g a s) * Real.sin (2 * N * s)‖ ≤ 2 * |a| := by
    intro s hs
    rw [Set.uIoc_of_le hu0, Set.mem_Ioc] at hs
    have hslt : s < δ₀ := lt_of_le_of_lt (le_trans hs.2 huδ) hδ0
    have hg := hδ₀bound s hs.1 hslt
    have hsin : |Real.sin (2 * N * s)| ≤ 1 := Real.abs_sin_le_one _
    rw [Real.norm_eq_abs, abs_mul]
    calc |entry1_g a s| * |Real.sin (2 * N * s)|
        ≤ (2 * |a|) * 1 := mul_le_mul hg hsin (by positivity) (by positivity)
      _ = 2 * |a| := mul_one _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hu0] at hnorm
  exact hnorm

theorem entry1_integrand_continuousOn (a : ℝ) (N : ℕ) (B : ℝ)
    (hB : B < Real.pi) :
    ContinuousOn (fun s => (entry1_g a s) * Real.sin (2 * N * s))
      (Set.Icc 0 B) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    have hval : (entry1_g a 0) * Real.sin (2 * (N : ℝ) * 0) = 0 := by
      simp [entry1_g]
    change Tendsto (fun s => (entry1_g a s) * Real.sin (2 * N * s))
      (𝓝[Set.Icc 0 B] 0) (𝓝 ((entry1_g a 0) * Real.sin (2 * (N : ℝ) * 0)))
    rw [hval]
    exact entry1_integrand_tendsto_zero a N B
  · have hspos : 0 < s := lt_of_le_of_ne (Set.mem_Icc.mp hs).1 (Ne.symm hs0)
    have hsin : Real.sin s ≠ 0 := by
      have hlt : s < Real.pi := lt_of_le_of_lt (Set.mem_Icc.mp hs).2 hB
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hspos hlt)
    have hg : ContinuousAt (entry1_g a) s := by
      have h1 : ContinuousAt (fun t => Real.sin (a * t)) s :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
      have h2 : ContinuousAt Real.sin s := Real.continuous_sin.continuousAt
      have hdiv := h1.div h2 hsin
      unfold entry1_g at hdiv ⊢
      exact hdiv
    have hsin2 : ContinuousAt (fun t => Real.sin (2 * N * t)) s :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt
    exact (hg.mul hsin2).continuousWithinAt

theorem entry1_parts_bound (a : ℝ) (N : ℕ) (hN : 1 ≤ N) (δ v : ℝ)
    (hδ : 0 < δ) (hδv : δ ≤ v) (hB : v < Real.pi) (M₂ : ℝ)
    (hM₂ : ∀ s ∈ Set.Icc δ v, |entry1_g' a s| ≤ M₂) :
    |∫ s in δ..v, (entry1_g a s) * Real.sin (2 * N * s)| ≤
      (|entry1_g a v| + |entry1_g a δ| + (v - δ) * M₂) / (2 * N) := by
  have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hN
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have h2Nne : (2 : ℝ) * (N : ℝ) ≠ 0 := ne_of_gt h2N
  have hw : ∀ s : ℝ, HasDerivAt (fun t => -Real.cos (2 * N * t) / (2 * N))
      (Real.sin (2 * N * s)) s := by
    intro s
    have h1 : HasDerivAt (fun t => (2 : ℝ) * N * t) (2 * N) s :=
      entry1_hasDerivAt_mul (2 * N) s
    have h2 := h1.cos
    have h3 := h2.neg
    have h4 := h3.div_const (2 * (N : ℝ))
    have hder : (-(-Real.sin (2 * ↑N * s) * (2 * ↑N)) / (2 * ↑N)) =
        Real.sin (2 * ↑N * s) := by
      rw [← neg_mul, neg_neg, mul_div_cancel_right₀ _ h2Nne]
    rwa [hder] at h4
  have huIcc : Set.uIcc δ v = Set.Icc δ v := Set.uIcc_of_le hδv
  have hu : ∀ x ∈ Set.uIcc δ v, HasDerivAt (entry1_g a) (entry1_g' a x) x := by
    intro x hx
    rw [huIcc] at hx
    exact entry1_g_hasDerivAt a x (entry1_sin_ne_of_mem δ v x hδ hB hx)
  have hv : ∀ x ∈ Set.uIcc δ v,
      HasDerivAt (fun t => -Real.cos (2 * N * t) / (2 * N))
        (Real.sin (2 * N * x)) x := fun x _ => hw x
  have hu' : IntervalIntegrable (entry1_g' a) volume δ v :=
    (entry1_g'_continuousOn a δ v hδ hB).intervalIntegrable_of_Icc hδv
  have hv' : IntervalIntegrable (fun s => Real.sin (2 * N * s)) volume δ v := by
    have hcont : ContinuousOn (fun s => Real.sin (2 * N * s)) (Set.Icc δ v) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    exact hcont.intervalIntegrable_of_Icc hδv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hEq : (∫ s in δ..v, (entry1_g a s) * Real.sin (2 * N * s)) =
      (entry1_g a v * (-Real.cos (2 * N * v) / (2 * N)) -
        entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N)) -
        ∫ s in δ..v, (entry1_g' a s) * (-Real.cos (2 * N * s) / (2 * N))) :=
    hparts
  have hbound_v : ∀ s : ℝ, |(-Real.cos (2 * N * s) / (2 * N))| ≤ 1 / (2 * N) := by
    intro s
    rw [abs_div, abs_neg]
    have hcos : |Real.cos (2 * N * s)| ≤ 1 := Real.abs_cos_le_one _
    have h2N' : |(2 : ℝ) * N| = 2 * N := abs_of_pos h2N
    rw [h2N']
    exact (div_le_div_iff_of_pos_right h2N).mpr hcos
  have hbound_bdry : |entry1_g a v * (-Real.cos (2 * N * v) / (2 * N)) -
      entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N))| ≤
      (|entry1_g a v| + |entry1_g a δ|) / (2 * N) := by
    calc |entry1_g a v * (-Real.cos (2 * N * v) / (2 * N)) -
          entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N))|
        ≤ |entry1_g a v * (-Real.cos (2 * N * v) / (2 * N))| +
            |entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N))| :=
          entry1_abs_sub_le _ _
      _ ≤ |entry1_g a v| * (1 / (2 * N)) + |entry1_g a δ| * (1 / (2 * N)) := by
          apply add_le_add
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hbound_v v) (abs_nonneg _)
          · rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hbound_v δ) (abs_nonneg _)
      _ = (|entry1_g a v| + |entry1_g a δ|) / (2 * N) := by ring
  have hδmem : δ ∈ Set.Icc δ v := ⟨le_rfl, hδv⟩
  have hM₂nn : (0 : ℝ) ≤ M₂ := le_trans (abs_nonneg _) (hM₂ δ hδmem)
  have hbound_int : |∫ s in δ..v,
      (entry1_g' a s) * (-Real.cos (2 * N * s) / (2 * N))| ≤
      ((v - δ) * M₂) / (2 * N) := by
    have hpt : ∀ s ∈ Set.uIoc δ v,
        ‖(entry1_g' a s) * (-Real.cos (2 * N * s) / (2 * N))‖ ≤ M₂ / (2 * N) := by
      intro s hs
      rw [Set.uIoc_of_le hδv, Set.mem_Ioc] at hs
      have hsIcc : s ∈ Set.Icc δ v := ⟨le_of_lt hs.1, hs.2⟩
      have h1 : |entry1_g' a s| ≤ M₂ := hM₂ s hsIcc
      have h2 : |(-Real.cos (2 * N * s) / (2 * N))| ≤ 1 / (2 * N) := hbound_v s
      rw [Real.norm_eq_abs, abs_mul]
      calc |entry1_g' a s| * |(-Real.cos (2 * N * s) / (2 * N))|
          ≤ M₂ * (1 / (2 * N)) :=
            mul_le_mul h1 h2 (by positivity) hM₂nn
        _ = M₂ / (2 * N) := by ring
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs] at hnorm
    have hvδ : |v - δ| = v - δ := abs_of_nonneg (by linarith)
    rw [hvδ] at hnorm
    have heq : (M₂ / (2 * N)) * (v - δ) = ((v - δ) * M₂) / (2 * N) := by ring
    rwa [heq] at hnorm
  rw [hEq]
  calc |(entry1_g a v * (-Real.cos (2 * N * v) / (2 * N)) -
        entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N))) -
        ∫ s in δ..v, (entry1_g' a s) * (-Real.cos (2 * N * s) / (2 * N))|
      ≤ |entry1_g a v * (-Real.cos (2 * N * v) / (2 * N)) -
          entry1_g a δ * (-Real.cos (2 * N * δ) / (2 * N))| +
          |∫ s in δ..v, (entry1_g' a s) * (-Real.cos (2 * N * s) / (2 * N))| :=
        entry1_abs_sub_le _ _
    _ ≤ (|entry1_g a v| + |entry1_g a δ|) / (2 * N) + ((v - δ) * M₂) / (2 * N) :=
        add_le_add hbound_bdry hbound_int
    _ = (|entry1_g a v| + |entry1_g a δ| + (v - δ) * M₂) / (2 * N) := by ring

theorem entry1_integral_sin_mul (c u : ℝ) (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..u, Real.sin (c * s)) = (1 - Real.cos (c * u)) / c := by
  have hderiv : ∀ s ∈ Set.uIcc 0 u,
      HasDerivAt (fun t => -Real.cos (c * t) / c) (Real.sin (c * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun t => c * t) c s := entry1_hasDerivAt_mul c s
    have h2 := h1.cos
    have h3 := h2.neg
    have h4 := h3.div_const c
    have hder : (-(-Real.sin (c * s) * c) / c) = Real.sin (c * s) := by
      rw [← neg_mul, neg_neg, mul_div_cancel_right₀ _ hc]
    rwa [hder] at h4
  have hint : IntervalIntegrable (fun s => Real.sin (c * s)) volume 0 u :=
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 u
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  simp only [mul_zero, Real.cos_zero]
  ring

theorem entry1_sin_diff (m a s : ℝ) :
    Real.sin ((m + a) * s) - Real.sin ((m - a) * s) =
      2 * Real.cos (m * s) * Real.sin (a * s) := by
  have e1 : (m + a) * s = m * s + a * s := by ring
  have e2 : (m - a) * s = m * s - a * s := by ring
  rw [e1, e2, Real.sin_add, Real.sin_sub]
  ring

theorem entry1_sum_sin_identity (N : ℕ) (a s : ℝ) (hs : |s| < Real.pi) :
    (∑ k ∈ range N, Real.sin ((((2 * k + 1 : ℕ) : ℝ) + a) * s)) -
      (∑ k ∈ range N, Real.sin ((((2 * k + 1 : ℕ) : ℝ) - a) * s)) =
      (entry1_g a s) * Real.sin (2 * N * s) := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [entry1_g]
  · have hsin : Real.sin s ≠ 0 := by
      by_cases hsp : 0 < s
      · have hlt : s < Real.pi := by
          have habs : |s| < Real.pi := hs
          have hle : s ≤ |s| := le_abs_self s
          linarith
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hsp hlt)
      · have hneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hsp) hs0
        have h1 : (0 : ℝ) < -s := neg_pos.mpr hneg
        have h2 : -s < Real.pi := by
          have habs : |s| < Real.pi := hs
          rw [abs_of_neg hneg] at habs
          exact habs
        have hpos := Real.sin_pos_of_pos_of_lt_pi h1 h2
        have hneg2 : Real.sin s = -Real.sin (-s) := by
          rw [Real.sin_neg, neg_neg]
        rw [hneg2]
        exact neg_ne_zero.mpr (ne_of_gt hpos)
    have htrig : ∀ k ∈ range N,
        Real.sin ((((2 * k + 1 : ℕ) : ℝ) + a) * s) -
          Real.sin ((((2 * k + 1 : ℕ) : ℝ) - a) * s) =
          2 * Real.cos ((((2 * k + 1 : ℕ) : ℝ)) * s) * Real.sin (a * s) :=
      fun k _ => entry1_sin_diff _ _ _
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl htrig,
      ← Finset.sum_mul, ← Finset.mul_sum, entry1_dirichlet N s hsin]
    have h2sin : (2 : ℝ) * Real.sin s ≠ 0 :=
      mul_ne_zero (by norm_num) hsin
    unfold entry1_g
    field_simp

theorem entry1_base_identity (N : ℕ) (a u : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hu : |u| < Real.pi) :
    (∑ k ∈ range N, chapter9Entry1CosineTerm 1 a u k) -
      (∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k) =
      ∫ s in (0 : ℝ)..u, (entry1_g a s) * Real.sin (2 * N * s) := by
  have hper_k : ∀ k ∈ range N,
      chapter9Entry1CosineTerm 1 a u k - chapter9Entry1ConstantTerm 1 a k =
        (∫ s in (0 : ℝ)..u, Real.sin ((((2 * k + 1 : ℕ) : ℝ) + a) * s)) -
          (∫ s in (0 : ℝ)..u, Real.sin ((((2 * k + 1 : ℕ) : ℝ) - a) * s)) := by
    intro k _
    have hA : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := entry1_sub_ne_zero a ha k
    have hB : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := entry1_add_ne_zero a ha k
    have eA := entry1_integral_sin_mul (((2 * k + 1 : ℕ) : ℝ) - a) u hA
    have eB := entry1_integral_sin_mul (((2 * k + 1 : ℕ) : ℝ) + a) u hB
    unfold chapter9Entry1CosineTerm chapter9Entry1ConstantTerm
    simp only [pow_one]
    rw [eA, eB]
    ring
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hper_k,
    Finset.sum_sub_distrib]
  have hswap : ∀ (sgn : ℝ),
      (∑ k ∈ range N, ∫ s in (0 : ℝ)..u,
        Real.sin ((((2 * k + 1 : ℕ) : ℝ) + sgn * a) * s)) =
      ∫ s in (0 : ℝ)..u, ∑ k ∈ range N,
        Real.sin ((((2 * k + 1 : ℕ) : ℝ) + sgn * a) * s) := by
    intro sgn
    symm
    apply intervalIntegral.integral_finsetSum
    intro k _
    exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 u
  have hswapB := hswap 1
  have hswapA := hswap (-1)
  simp only [one_mul] at hswapB
  simp only [neg_one_mul, ← sub_eq_add_neg] at hswapA
  have hintB : IntervalIntegrable
      (fun s => ∑ k ∈ range N, Real.sin ((((2 * k + 1 : ℕ) : ℝ) + a) * s))
      volume 0 u := by
    apply Continuous.intervalIntegrable _ 0 u
    apply continuous_finsetSum
    intro k _
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hintA : IntervalIntegrable
      (fun s => ∑ k ∈ range N, Real.sin ((((2 * k + 1 : ℕ) : ℝ) - a) * s))
      volume 0 u := by
    apply Continuous.intervalIntegrable _ 0 u
    apply continuous_finsetSum
    intro k _
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id)
  rw [hswapB, hswapA, ← intervalIntegral.integral_sub hintB hintA]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsabs : |s| < Real.pi := by
    have hmem : s ∈ Set.uIcc 0 u := hs
    rw [Set.mem_uIcc] at hmem
    have hle : |s| ≤ |u| := by
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hsnn : 0 ≤ s := h1
        rw [abs_of_nonneg hsnn]
        exact le_trans h2 (le_abs_self u)
      · have hsn : s ≤ 0 := h2
        rw [abs_of_nonpos hsn]
        exact le_trans (neg_le_neg h1) (neg_le_abs u)
    linarith [hle, hu]
  exact entry1_sum_sin_identity N a s hsabs

theorem entry1_integrand_odd (a : ℝ) (N : ℕ) (s : ℝ) :
    (entry1_g a (-s)) * Real.sin (2 * N * (-s)) =
      -((entry1_g a s) * Real.sin (2 * N * s)) := by
  unfold entry1_g
  have e1 : Real.sin (a * (-s)) = -Real.sin (a * s) := by
    rw [mul_neg, Real.sin_neg]
  have e2 : Real.sin (-s) = -Real.sin s := Real.sin_neg s
  have e3 : Real.sin (2 * N * (-s)) = -Real.sin (2 * N * s) := by
    have heq : (2 : ℝ) * N * (-s) = -((2 : ℝ) * N * s) := by ring
    rw [heq, Real.sin_neg]
  rw [e1, e2, e3, neg_div_neg_eq]
  ring

theorem entry1_odd_integral (h : ℝ → ℝ)
    (hodd : ∀ s, h (-s) = -h s) (u : ℝ) :
    (∫ s in (0 : ℝ)..u, h s) = ∫ s in (0 : ℝ)..|u|, h s := by
  by_cases hu0 : 0 ≤ u
  · rw [abs_of_nonneg hu0]
  · have hu0' : u < 0 := not_le.mp hu0
    have habs : |u| = -u := abs_of_neg hu0'
    rw [habs]
    have hcomp := intervalIntegral.integral_comp_neg (a := 0) (b := u) (f := h)
    have hodd_int : (∫ x in (0 : ℝ)..u, h (-x)) = -(∫ x in (0 : ℝ)..u, h x) := by
      have hfun : (fun x => h (-x)) = (fun x => -h x) := funext hodd
      rw [hfun, intervalIntegral.integral_neg]
    rw [hodd_int] at hcomp
    have hsymm : (∫ x in -u..-(0 : ℝ), h x) = -(∫ x in (0 : ℝ)..-u, h x) := by
      rw [intervalIntegral.integral_symm]
      simp only [neg_zero]
    rw [hsymm] at hcomp
    exact neg_injective hcomp

theorem entry1_rl_nonneg (a : ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hBpi : B < Real.pi) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ v ∈ Set.Icc 0 B,
      |∫ s in (0 : ℝ)..v, (entry1_g a s) * Real.sin (2 * N * s)| ≤ ε := by
  intro ε hε
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, fun N _ v _ => ?_⟩
    have hzero : ∀ s : ℝ, (entry1_g 0 s) * Real.sin (2 * N * s) = 0 := by
      intro s
      simp [entry1_g]
    have hfun : (fun s => (entry1_g 0 s) * Real.sin (2 * N * s)) = fun _ => 0 :=
      funext hzero
    rw [hfun, intervalIntegral.integral_const, smul_zero, abs_zero]
    exact hε.le
  · by_cases hB0' : B = 0
    · subst hB0'
      refine ⟨1, fun N _ v hv => ?_⟩
      rw [Set.mem_Icc] at hv
      have hv0 : v = 0 := le_antisymm hv.2 hv.1
      rw [hv0, intervalIntegral.integral_same, abs_zero]
      exact hε.le
    · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB0')
      have hapos : (0 : ℝ) < |a| := abs_pos.mpr ha0
      obtain ⟨δ₀, hδ₀pos, hδ₀bound⟩ := entry1_g_bound_near_zero a
      set δ : ℝ := min (min (δ₀ / 2) (ε / (4 * |a|))) B with hδdef
      have hδpos : 0 < δ := by
        have h1 : (0 : ℝ) < δ₀ / 2 := by linarith
        have h2 : (0 : ℝ) < ε / (4 * |a|) :=
          div_pos hε (mul_pos (by norm_num) hapos)
        have h3 : (0 : ℝ) < min (δ₀ / 2) (ε / (4 * |a|)) := lt_min h1 h2
        rw [hδdef]
        exact lt_min h3 hBpos
      have hδ0 : δ < δ₀ := by
        have h1 : δ ≤ δ₀ / 2 := by
          rw [hδdef]
          exact le_trans (min_le_left _ _) (min_le_left _ _)
        linarith
      have hδε : δ * (2 * |a|) ≤ ε / 2 := by
        have h1 : δ ≤ ε / (4 * |a|) := by
          rw [hδdef]
          exact le_trans (min_le_left _ _) (min_le_right _ _)
        have h4a : (0 : ℝ) < 4 * |a| := mul_pos (by norm_num) hapos
        have h2 : δ * (4 * |a|) ≤ ε := (le_div_iff₀ h4a).mp h1
        linarith
      have hδB : δ ≤ B := by
        rw [hδdef]
        exact min_le_right _ _
      have hne : (Set.Icc δ B).Nonempty := ⟨δ, le_rfl, hδB⟩
      have hcont_g : ContinuousOn (fun s => |entry1_g a s|) (Set.Icc δ B) :=
        (entry1_g_continuousOn a δ B hδpos hBpi).abs
      obtain ⟨x₁, -, hx₁max⟩ := isCompact_Icc.exists_isMaxOn hne hcont_g
      have hcont_g' : ContinuousOn (fun s => |entry1_g' a s|) (Set.Icc δ B) :=
        (entry1_g'_continuousOn a δ B hδpos hBpi).abs
      obtain ⟨x₂, -, hx₂max⟩ := isCompact_Icc.exists_isMaxOn hne hcont_g'
      set M₁ : ℝ := |entry1_g a x₁| with hM₁def
      set M₂ : ℝ := |entry1_g' a x₂| with hM₂def
      have hM₁ : ∀ s ∈ Set.Icc δ B, |entry1_g a s| ≤ M₁ := by
        intro s hs
        rw [hM₁def]
        exact hx₁max hs
      have hM₂ : ∀ s ∈ Set.Icc δ B, |entry1_g' a s| ≤ M₂ := by
        intro s hs
        rw [hM₂def]
        exact hx₂max hs
      have hM₁nn : (0 : ℝ) ≤ M₁ := by
        rw [hM₁def]
        exact abs_nonneg _
      have hM₂nn : (0 : ℝ) ≤ M₂ := by
        rw [hM₂def]
        exact abs_nonneg _
      set C₁ : ℝ := M₁ + M₁ + B * M₂ with hC₁def
      obtain ⟨N₁, hN₁⟩ := exists_nat_gt (C₁ / ε)
      refine ⟨max N₁ 1, fun N hN v hv => ?_⟩
      have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
      have hNN₁ : (C₁ / ε) < (N : ℝ) := by
        have h2 : (N₁ : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast le_trans (le_max_left _ _) hN
        linarith [hN₁]
      have hv0 : 0 ≤ v := (Set.mem_Icc.mp hv).1
      have hvB : v ≤ B := (Set.mem_Icc.mp hv).2
      by_cases hvδ : v ≤ δ
      · have hbd := entry1_near_zero_integral_bound a N δ₀ hδ₀bound v δ
          hv0 hvδ hδ0
        have hle1 : (2 * |a|) * v ≤ (2 * |a|) * δ :=
          mul_le_mul_of_nonneg_left hvδ (by positivity)
        have hle2 : (2 * |a|) * δ ≤ ε / 2 := by
          rw [mul_comm (2 * |a|) δ]
          exact hδε
        linarith [hbd, hle1, hle2, hε]
      · have hvδlt : δ < v := not_le.mp hvδ
        have hvδle : δ ≤ v := le_of_lt hvδlt
        have hcont_all := entry1_integrand_continuousOn a N B hBpi
        have hint0 : IntervalIntegrable
            (fun s => (entry1_g a s) * Real.sin (2 * N * s)) volume 0 δ := by
          have hsub : Set.Icc 0 δ ⊆ Set.Icc 0 B := by
            intro s hs
            rw [Set.mem_Icc] at hs ⊢
            exact ⟨hs.1, le_trans hs.2 hδB⟩
          exact (hcont_all.mono hsub).intervalIntegrable_of_Icc hδpos.le
        have hint1 : IntervalIntegrable
            (fun s => (entry1_g a s) * Real.sin (2 * N * s)) volume δ v := by
          have hsub : Set.Icc δ v ⊆ Set.Icc 0 B := by
            intro s hs
            rw [Set.mem_Icc] at hs ⊢
            exact ⟨le_trans hδpos.le hs.1, le_trans hs.2 hvB⟩
          exact (hcont_all.mono hsub).intervalIntegrable_of_Icc hvδle
        have hsplit := intervalIntegral.integral_add_adjacent_intervals hint0 hint1
        have hbd0 := entry1_near_zero_integral_bound a N δ₀ hδ₀bound δ δ
          hδpos.le le_rfl hδ0
        have hbd0' : |∫ s in (0 : ℝ)..δ,
            (entry1_g a s) * Real.sin (2 * N * s)| ≤ ε / 2 := by
          have hle : (2 * |a|) * δ ≤ ε / 2 := by
            rw [mul_comm (2 * |a|) δ]
            exact hδε
          linarith [hbd0, hle]
        have hM₂v : ∀ s ∈ Set.Icc δ v, |entry1_g' a s| ≤ M₂ := by
          intro s hs
          apply hM₂ s
          rw [Set.mem_Icc] at hs ⊢
          exact ⟨hs.1, le_trans hs.2 hvB⟩
        have hparts := entry1_parts_bound a N hN1 δ v hδpos hvδle
          (lt_of_le_of_lt hvB hBpi) M₂ hM₂v
        have hg_v : |entry1_g a v| ≤ M₁ := hM₁ v ⟨hvδle, hvB⟩
        have hg_δ : |entry1_g a δ| ≤ M₁ := hM₁ δ ⟨le_rfl, hδB⟩
        have hvdM : (v - δ) * M₂ ≤ B * M₂ :=
          mul_le_mul_of_nonneg_right (by linarith) hM₂nn
        have hNp : (0 : ℝ) < (N : ℝ) := by
          exact_mod_cast lt_of_lt_of_le (by norm_num) hN1
        have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
        have hnum : |entry1_g a v| + |entry1_g a δ| + (v - δ) * M₂ ≤ C₁ := by
          rw [hC₁def]
          linarith [hg_v, hg_δ, hvdM]
        have hC₁N : C₁ ≤ ε * (N : ℝ) := by
          have hlt := (div_lt_iff₀ hε).mp hNN₁
          linarith
        have hle : (|entry1_g a v| + |entry1_g a δ| + (v - δ) * M₂) / (2 * N) ≤
            ε / 2 := by
          have h2 : C₁ / (2 * N) ≤ ε / 2 := by
            rw [div_le_iff₀ h2N]
            have heq : (ε / 2) * (2 * (N : ℝ)) = ε * (N : ℝ) := by ring
            rw [heq]
            exact hC₁N
          calc (|entry1_g a v| + |entry1_g a δ| + (v - δ) * M₂) / (2 * N)
              ≤ C₁ / (2 * N) := (div_le_div_iff_of_pos_right h2N).mpr hnum
            _ ≤ ε / 2 := h2
        have hparts_le : |∫ s in δ..v,
            (entry1_g a s) * Real.sin (2 * N * s)| ≤ ε / 2 :=
          le_trans hparts hle
        rw [← hsplit]
        calc |(∫ s in (0 : ℝ)..δ, (entry1_g a s) * Real.sin (2 * N * s)) +
              (∫ s in δ..v, (entry1_g a s) * Real.sin (2 * N * s))|
            ≤ |∫ s in (0 : ℝ)..δ, (entry1_g a s) * Real.sin (2 * N * s)| +
                |∫ s in δ..v, (entry1_g a s) * Real.sin (2 * N * s)| :=
              abs_add_le _ _
          _ ≤ ε / 2 + ε / 2 := add_le_add hbd0' hparts_le
          _ = ε := by ring

theorem entry1_r1_tendsto (a u : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) (hu : |u| < Real.pi) :
    Tendsto (fun N => ∑ k ∈ range N, chapter9Entry1CosineTerm 1 a u k)
      atTop (𝓝 (chapter9Entry1Constant 1 a)) := by
  have hsum : Summable (chapter9Entry1ConstantTerm 1 a) :=
    entry1_const_summable 1 a (by norm_num)
  have hC : Tendsto (fun N => ∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k)
      atTop (𝓝 (∑' k, chapter9Entry1ConstantTerm 1 a k)) :=
    hsum.tendsto_sum_tsum_nat
  have hR0 : Tendsto
      (fun N : ℕ => ∫ s in (0 : ℝ)..u, (entry1_g a s) * Real.sin (2 * N * s))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨N₀, hN₀⟩ := entry1_rl_nonneg a |u| (abs_nonneg _) hu (ε / 2) hε2
    refine ⟨N₀, fun N hN => ?_⟩
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
    have hodd := entry1_odd_integral
      (fun s => (entry1_g a s) * Real.sin (2 * N * s))
      (entry1_integrand_odd a N) u
    rw [hodd]
    have hmem : |u| ∈ Set.Icc 0 |u| := ⟨abs_nonneg _, le_rfl⟩
    have hle := hN₀ N hN |u| hmem
    linarith [hle, hε]
  have hdecomp : ∀ N : ℕ, (∑ k ∈ range N, chapter9Entry1CosineTerm 1 a u k) =
      (∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k) +
        (∫ s in (0 : ℝ)..u, (entry1_g a s) * Real.sin (2 * N * s)) := by
    intro N
    have hbase := entry1_base_identity N a u ha hu
    linear_combination hbase
  have hadd := hC.add hR0
  have hC0 : (∑' k, chapter9Entry1ConstantTerm 1 a k) + 0 =
      chapter9Entry1Constant 1 a := by
    unfold chapter9Entry1Constant
    ring
  rw [hC0] at hadd
  have hfun : (fun N : ℕ => ∑ k ∈ range N, chapter9Entry1CosineTerm 1 a u k) =
      (fun N : ℕ => (∑ k ∈ range N, chapter9Entry1ConstantTerm 1 a k) +
        (∫ s in (0 : ℝ)..u, (entry1_g a s) * Real.sin (2 * N * s))) :=
    funext hdecomp
  rw [hfun]
  exact hadd

theorem entry1_integral_cos_mul (c u : ℝ) (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..u, Real.cos (c * s)) = Real.sin (c * u) / c := by
  have hderiv : ∀ s ∈ Set.uIcc 0 u,
      HasDerivAt (fun t => Real.sin (c * t) / c) (Real.cos (c * s)) s := by
    intro s _
    have h1 : HasDerivAt (fun t => c * t) c s := entry1_hasDerivAt_mul c s
    have h2 := h1.sin
    have h4 := h2.div_const c
    have hder : (Real.cos (c * s) * c / c) = Real.cos (c * s) := by
      rw [mul_div_cancel_right₀ _ hc]
    rwa [hder] at h4
  have hint : IntervalIntegrable (fun s => Real.cos (c * s)) volume 0 u :=
    (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 u
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  simp only [mul_zero, Real.sin_zero, zero_div, sub_zero]

theorem entry1_integral_pow (n : ℕ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, t ^ n) = x ^ (n + 1) / ((n : ℝ) + 1) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ s ∈ Set.uIcc 0 x,
      HasDerivAt (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1)) (s ^ n) s := by
    intro s _
    have h1 : HasDerivAt (fun t : ℝ => t ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * s ^ n) s := by
      have hpow := hasDerivAt_pow (n + 1) (s : ℝ)
      simpa [pow_succ', Nat.cast_add, Nat.cast_one] using hpow
    have h2 := h1.div_const ((n : ℝ) + 1)
    have hder : (((n + 1 : ℕ) : ℝ) * s ^ n / ((n : ℝ) + 1)) = s ^ n := by
      have hcast : (((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1) := by push_cast; ring
      rw [hcast]
      field_simp
    rwa [hder] at h2
  have hcont : Continuous (fun t : ℝ => t ^ n) := continuous_id.pow n
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n) volume 0 x :=
    hcont.intervalIntegrable 0 x
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : (0 : ℝ) ^ (n + 1) = 0 := zero_pow (Nat.succ_ne_zero n)
  rw [hftc, h0, zero_div, sub_zero]

theorem entry1_cosTerm_continuous (s : ℕ) (a : ℝ) (k : ℕ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    Continuous (fun t : ℝ => chapter9Entry1CosineTerm s a t k) := by
  unfold chapter9Entry1CosineTerm
  have hA : ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s) ≠ 0 :=
    pow_ne_zero s (entry1_sub_ne_zero a ha k)
  have hB : ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s) ≠ 0 :=
    pow_ne_zero s (entry1_add_ne_zero a ha k)
  have h1 : Continuous (fun t : ℝ => Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hA)
  have h2 : Continuous (fun t : ℝ => Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hB)
  exact h1.sub h2

theorem entry1_sinTerm_continuous (s : ℕ) (a : ℝ) (k : ℕ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    Continuous (fun t : ℝ => chapter9Entry1SineTerm s a t k) := by
  unfold chapter9Entry1SineTerm
  have hA : ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s) ≠ 0 :=
    pow_ne_zero s (entry1_sub_ne_zero a ha k)
  have hB : ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s) ≠ 0 :=
    pow_ne_zero s (entry1_add_ne_zero a ha k)
  have h1 : Continuous (fun t : ℝ => Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hA)
  have h2 : Continuous (fun t : ℝ => Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hB)
  exact h1.sub h2

theorem entry1_cosTerm_integral (s : ℕ) (a x : ℝ) (k : ℕ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∫ t in (0 : ℝ)..x, chapter9Entry1CosineTerm s a t k) =
      chapter9Entry1SineTerm (s + 1) a x k := by
  have hA : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := entry1_sub_ne_zero a ha k
  have hB : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := entry1_add_ne_zero a ha k
  have hpowA : ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s) ≠ 0 := pow_ne_zero s hA
  have hpowB : ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s) ≠ 0 := pow_ne_zero s hB
  have hcontA : Continuous (fun t : ℝ =>
      Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hpowA)
  have hcontB : Continuous (fun t : ℝ =>
      Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hpowB)
  have hintA : IntervalIntegrable (fun t : ℝ =>
      Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) volume 0 x :=
    hcontA.intervalIntegrable 0 x
  have hintB : IntervalIntegrable (fun t : ℝ =>
      Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) volume 0 x :=
    hcontB.intervalIntegrable 0 x
  have hsub : (∫ t in (0 : ℝ)..x, chapter9Entry1CosineTerm s a t k) =
      (∫ t in (0 : ℝ)..x, Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) -
      (∫ t in (0 : ℝ)..x, Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) := by
    unfold chapter9Entry1CosineTerm
    rw [intervalIntegral.integral_sub hintA hintB]
  have hAeq : (∫ t in (0 : ℝ)..x, Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) =
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ (s + 1)) := by
    have hfun : (fun t : ℝ => Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) =
        (fun t : ℝ => (1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) *
          Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * t))) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      entry1_integral_cos_mul _ _ hA, pow_succ]
    field_simp
  have hBeq : (∫ t in (0 : ℝ)..x, Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) =
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ (s + 1)) := by
    have hfun : (fun t : ℝ => Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) =
        (fun t : ℝ => (1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) *
          Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * t))) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      entry1_integral_cos_mul _ _ hB, pow_succ]
    field_simp
  rw [hsub, hAeq, hBeq]
  unfold chapter9Entry1SineTerm
  rfl

theorem entry1_sinTerm_integral (s : ℕ) (a x : ℝ) (k : ℕ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∫ t in (0 : ℝ)..x, chapter9Entry1SineTerm s a t k) =
      chapter9Entry1ConstantTerm (s + 1) a k -
        chapter9Entry1CosineTerm (s + 1) a x k := by
  have hA : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := entry1_sub_ne_zero a ha k
  have hB : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := entry1_add_ne_zero a ha k
  have hpowA : ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s) ≠ 0 := pow_ne_zero s hA
  have hpowB : ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s) ≠ 0 := pow_ne_zero s hB
  have hpowA1 : ((((2 * k + 1 : ℕ) : ℝ) - a) ^ (s + 1)) ≠ 0 :=
    pow_ne_zero _ hA
  have hpowB1 : ((((2 * k + 1 : ℕ) : ℝ) + a) ^ (s + 1)) ≠ 0 :=
    pow_ne_zero _ hB
  have hcontA : Continuous (fun t : ℝ =>
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hpowA)
  have hcontB : Continuous (fun t : ℝ =>
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div
      continuous_const (fun _ => hpowB)
  have hintA : IntervalIntegrable (fun t : ℝ =>
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) volume 0 x :=
    hcontA.intervalIntegrable 0 x
  have hintB : IntervalIntegrable (fun t : ℝ =>
      Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) volume 0 x :=
    hcontB.intervalIntegrable 0 x
  have hsub : (∫ t in (0 : ℝ)..x, chapter9Entry1SineTerm s a t k) =
      (∫ t in (0 : ℝ)..x, Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) -
      (∫ t in (0 : ℝ)..x, Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) := by
    unfold chapter9Entry1SineTerm
    rw [intervalIntegral.integral_sub hintA hintB]
  have hAeq : (∫ t in (0 : ℝ)..x, Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) =
      1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ (s + 1)) -
        Real.cos (((((2 * k + 1 : ℕ) : ℝ) - a) * x)) /
          ((((2 * k + 1 : ℕ) : ℝ) - a) ^ (s + 1)) := by
    have hfun : (fun t : ℝ => Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) =
        (fun t : ℝ => (1 / ((((2 * k + 1 : ℕ) : ℝ) - a) ^ s)) *
          Real.sin (((((2 * k + 1 : ℕ) : ℝ) - a) * t))) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      entry1_integral_sin_mul _ _ hA, pow_succ]
    field_simp
  have hBeq : (∫ t in (0 : ℝ)..x, Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
      ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) =
      1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ (s + 1)) -
        Real.cos (((((2 * k + 1 : ℕ) : ℝ) + a) * x)) /
          ((((2 * k + 1 : ℕ) : ℝ) + a) ^ (s + 1)) := by
    have hfun : (fun t : ℝ => Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t)) /
        ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) =
        (fun t : ℝ => (1 / ((((2 * k + 1 : ℕ) : ℝ) + a) ^ s)) *
          Real.sin (((((2 * k + 1 : ℕ) : ℝ) + a) * t))) := by
      funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul,
      entry1_integral_sin_mul _ _ hB, pow_succ]
    field_simp
  rw [hsub, hAeq, hBeq]
  unfold chapter9Entry1ConstantTerm chapter9Entry1CosineTerm
  ring

theorem entry1_sum_sine_eq (s N : ℕ) (a x : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∑ k ∈ range N, chapter9Entry1SineTerm (s + 1) a x k) =
      ∫ t in (0 : ℝ)..x, ∑ k ∈ range N, chapter9Entry1CosineTerm s a t k := by
  have hper : ∀ k ∈ range N, chapter9Entry1SineTerm (s + 1) a x k =
      ∫ t in (0 : ℝ)..x, chapter9Entry1CosineTerm s a t k :=
    fun k _ => (entry1_cosTerm_integral s a x k ha).symm
  rw [Finset.sum_congr rfl hper]
  symm
  apply intervalIntegral.integral_finsetSum
  intro k _
  exact (entry1_cosTerm_continuous s a k ha).intervalIntegrable 0 x

theorem entry1_sum_cosine_eq (s N : ℕ) (a x : ℝ)
    (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ)) :
    (∑ k ∈ range N, chapter9Entry1CosineTerm (s + 1) a x k) =
      (∑ k ∈ range N, chapter9Entry1ConstantTerm (s + 1) a k) -
        ∫ t in (0 : ℝ)..x, ∑ k ∈ range N, chapter9Entry1SineTerm s a t k := by
  have hper : ∀ k ∈ range N, chapter9Entry1CosineTerm (s + 1) a x k =
      chapter9Entry1ConstantTerm (s + 1) a k -
        ∫ t in (0 : ℝ)..x, chapter9Entry1SineTerm s a t k := by
    intro k _
    have h := entry1_sinTerm_integral s a x k ha
    linarith
  rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
  congr 1
  symm
  apply intervalIntegral.integral_finsetSum
  intro k _
  exact (entry1_sinTerm_continuous s a k ha).intervalIntegrable 0 x

end
end Entry1Logratio
end Ramanujan.Part1Ch9
end
