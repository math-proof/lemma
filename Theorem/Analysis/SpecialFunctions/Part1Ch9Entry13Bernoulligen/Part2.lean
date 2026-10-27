/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

theorem sin_half_ne_zero_of_mem {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) : Real.sin (u / 2) ≠ 0 := by
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨k, hk⟩ := hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu_eq : u = 2 * (k : ℝ) * Real.pi := by linarith
  have habs : |u| ≤ |x| := by
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hxnn : 0 ≤ x
      · calc |u| = u := abs_of_nonneg (by linarith)
          _ ≤ x := h2
          _ = |x| := (abs_of_nonneg hxnn).symm
      · have hxlt : x < 0 := lt_of_not_ge hxnn
        linarith
    · by_cases hxnn : x ≤ 0
      · calc |u| = -u := abs_of_nonpos (by linarith)
          _ ≤ -x := by linarith
          _ = |x| := (abs_of_nonpos hxnn).symm
      · have hxlt : 0 < x := lt_of_not_ge hxnn
        linarith
  have hk0 : (k : ℝ) ≠ 0 := by
    intro hk0'
    have : u = 0 := by
      rw [hu_eq, hk0']; ring
    exact hu0 this
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have hne : (k : ℤ) ≠ 0 := by
      intro hz; apply hk0; rw [hz]; simp
    have h1 : 1 ≤ |k| := Int.one_le_abs hne
    have h2 : ((1 : ℤ) : ℝ) ≤ (((|k| : ℤ)) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs] at h2
  have h2pi : 2 * Real.pi ≤ |u| := by
    rw [hu_eq]
    rw [show (2 * (k : ℝ) * Real.pi) = (2 * Real.pi) * (k : ℝ) from by ring]
    rw [abs_mul]
    have hnn : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi = (2 * Real.pi) * 1 := by ring
      _ ≤ (2 * Real.pi) * |(k : ℝ)| := by
          apply mul_le_mul_of_nonneg_left hk1 hnn
      _ = |2 * Real.pi| * |(k : ℝ)| := by rw [abs_of_nonneg hnn]
  linarith

theorem sin_div_tendsto :
    Filter.Tendsto (fun y : ℝ => Real.sin y / y)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h := (Real.hasDerivAt_sin 0).tendsto_slope
  rw [Real.cos_zero] at h
  have heq : ∀ y : ℝ, slope Real.sin 0 y = Real.sin y / y := by
    intro y
    simp [slope, sub_zero, Real.sin_zero, div_eq_inv_mul, smul_eq_mul]
  exact h.congr' (Eventually.of_forall (fun y => heq y))

theorem half_tendsto_punctured :
    Filter.Tendsto (fun u : ℝ => u / 2)
      (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ _ _
  · have hcont : Continuous (fun u : ℝ => u / 2) := by continuity
    have h0 : Filter.Tendsto (fun u : ℝ => u / 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (0 / 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0
  · filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
    exact div_ne_zero hu two_ne_zero

theorem sin_half_div_tendsto :
    Filter.Tendsto (fun u : ℝ => Real.sin (u / 2) / (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
  sin_div_tendsto.comp half_tendsto_punctured

theorem half_div_sin_tendsto :
    Filter.Tendsto (fun u : ℝ => (u / 2) / Real.sin (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have h := sin_half_div_tendsto.inv₀ one_ne_zero
  rw [inv_one] at h
  exact h.congr' (Eventually.of_forall (fun u => inv_div _ _))

theorem entry13_pointwise_eq (n : ℕ) (hn : 1 ≤ n) (u : ℝ) :
    chapter9Entry13Integrand n u =
      u ^ (n - 1) * Real.cos (u / 2) * ((u / 2) / Real.sin (u / 2)) := by
  unfold chapter9Entry13Integrand
  by_cases hs : Real.sin (u / 2) = 0
  · rw [hs, div_zero, div_zero, mul_zero, mul_zero]
  · have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hpow : u ^ n = u ^ (n - 1) * u := by
      have h := pow_succ u (n - 1)
      rwa [hns] at h
    rw [hpow]
    field_simp

theorem zero_pow_eq_entry13F0 (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℝ) ^ (n - 1) = entry13F0 n := by
  unfold entry13F0
  by_cases hn1 : n = 1
  · subst hn1; simp
  · have hne : n - 1 ≠ 0 := by omega
    simp only [hn1, ite_false]
    exact zero_pow hne

theorem entry13_tendsto (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (chapter9Entry13Integrand n)
      (nhdsWithin 0 {0}ᶜ) (nhds (entry13F0 n)) := by
  have hpow : Filter.Tendsto (fun u : ℝ => u ^ (n - 1))
      (nhdsWithin 0 {0}ᶜ) (nhds ((0 : ℝ) ^ (n - 1))) :=
    ((continuous_pow (n - 1)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hcos : Filter.Tendsto (fun u : ℝ => Real.cos (u / 2))
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have hc : Filter.Tendsto (fun u : ℝ => Real.cos (u / 2))
        (nhds (0 : ℝ)) (nhds (Real.cos (0 / 2))) :=
      (Real.continuous_cos.comp (by continuity : Continuous (fun u : ℝ => u / 2))).tendsto 0
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hprod := (hpow.mul hcos).mul half_div_sin_tendsto
  rw [zero_pow_eq_entry13F0 n hn] at hprod
  simp only [mul_one] at hprod
  exact hprod.congr' (Eventually.of_forall (fun u => (entry13_pointwise_eq n hn u).symm))

theorem entry13Ext_continuousAt_zero (n : ℕ) (hn : 1 ≤ n) :
    ContinuousAt (entry13Ext n) 0 := by
  have hg := entry13_tendsto n hn
  have heq : (entry13Ext n) =ᶠ[nhdsWithin 0 {0}ᶜ] (chapter9Entry13Integrand n) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    simp [entry13Ext, hu]
  have hF : Filter.Tendsto (entry13Ext n) (nhdsWithin 0 {0}ᶜ) (nhds (entry13F0 n)) :=
    hg.congr' heq.symm
  have h0 : Filter.Tendsto (entry13Ext n) (nhdsWithin 0 {0}) (nhds (entry13F0 n)) := by
    rw [nhdsWithin_singleton]
    have hthis : entry13Ext n 0 = entry13F0 n := by simp [entry13Ext]
    have hpu := tendsto_pure_nhds (entry13Ext n) 0
    rwa [hthis] at hpu
  have hall := hF.sup h0
  rw [← nhdsWithin_union, Set.compl_union_self, nhdsWithin_univ] at hall
  change Filter.Tendsto (entry13Ext n) (nhds 0) (nhds (entry13Ext n 0))
  have hval : entry13Ext n 0 = entry13F0 n := by simp [entry13Ext]
  rwa [hval]

theorem entry13Ext_continuousAt_of_ne (n : ℕ) (x : ℝ) (hx : |x| < 2 * Real.pi)
    (u : ℝ) (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    ContinuousAt (entry13Ext n) u := by
  have hsin := sin_half_ne_zero_of_mem hx hu hu0
  have hg : ContinuousAt (chapter9Entry13Integrand n) u := by
    unfold chapter9Entry13Integrand
    apply ContinuousAt.mul
    · exact (continuous_pow n).continuousAt.div_const 2
    · apply ContinuousAt.div
      · exact (Real.continuous_cos.comp
          (by continuity : Continuous (fun u : ℝ => u / 2))).continuousAt
      · exact (Real.continuous_sin.comp
          (by continuity : Continuous (fun u : ℝ => u / 2))).continuousAt
      · exact hsin
  have heq : (entry13Ext n) =ᶠ[nhds u] (chapter9Entry13Integrand n) := by
    have hmem : ({0}ᶜ : Set ℝ) ∈ nhds u := compl_singleton_mem_nhds hu0
    filter_upwards [hmem] with v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp [entry13Ext, hv]
  exact hg.congr heq.symm

theorem entry13Ext_continuousOn (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    ContinuousOn (entry13Ext n) (Set.uIcc 0 x) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0
    exact (entry13Ext_continuousAt_zero n hn).continuousWithinAt
  · exact (entry13Ext_continuousAt_of_ne n x hx u hu hu0).continuousWithinAt

theorem entry13_ae_eq (n : ℕ) (x : ℝ) :
    (chapter9Entry13Integrand n) =ᵐ[volume.restrict (Set.uIoc 0 x)] (entry13Ext n) := by
  change ∀ᵐ u ∂ (volume.restrict (Set.uIoc 0 x)),
    chapter9Entry13Integrand n u = entry13Ext n u
  rw [MeasureTheory.ae_iff]
  have hsub : {a | ¬ chapter9Entry13Integrand n a = entry13Ext n a} ⊆ ({0} : Set ℝ) := by
    intro u hu
    have hu : ¬ chapter9Entry13Integrand n u = entry13Ext n u := hu
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact hu (by simp [entry13Ext, hne])
  have h0 : (volume.restrict (Set.uIoc 0 x)) ({0} : Set ℝ) = 0 := by simp
  exact MeasureTheory.measure_mono_null hsub h0

theorem entry13_intervalIntegrable (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    IntervalIntegrable (chapter9Entry13Integrand n) volume 0 x := by
  have hF : IntervalIntegrable (entry13Ext n) volume 0 x :=
    (entry13Ext_continuousOn n x hn hx).intervalIntegrable
  exact (intervalIntegrable_congr_ae (entry13_ae_eq n x)).mpr hF

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
