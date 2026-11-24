module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Basic
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part5


public section

/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

theorem chap9G_zero : chap9G 0 = 1 := by
  simp [chap9G]

theorem chap9G_of_ne {t : ℝ} (ht : t ≠ 0) : chap9G t = Real.arcsin t / t := by
  simp [chap9G, ht]

theorem tendsto_arcsin_div_self_nhdsNE :
    Filter.Tendsto (fun t : ℝ => Real.arcsin t / t) (𝓝[≠] 0) (𝓝 1) := by
  have hderiv : HasDerivAt Real.arcsin 1 (0 : ℝ) := by
    have h := Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
    have h1 : (1 : ℝ) / Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 := by
      rw [show (1 : ℝ) - (0 : ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one, div_one]
    rwa [h1] at h
  have hslope := hderiv.tendsto_slope
  have hEq : (fun t : ℝ => Real.arcsin t / t) =ᶠ[𝓝[≠] (0 : ℝ)] slope Real.arcsin 0 :=
    Filter.Eventually.of_forall
      (fun t => by simp only [slope_def_field, Real.arcsin_zero, sub_zero])
  exact Filter.Tendsto.congr' hEq.symm hslope

theorem continuousAt_chap9G_zero : ContinuousAt chap9G 0 := by
  have hpunc : Filter.Tendsto chap9G (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hEq : chap9G =ᶠ[𝓝[≠] (0 : ℝ)] (fun t : ℝ => Real.arcsin t / t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      exact chap9G_of_ne ht
    exact Filter.Tendsto.congr' hEq.symm tendsto_arcsin_div_self_nhdsNE
  rw [Metric.continuousAt_iff]
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at hpunc
  obtain ⟨δ, hδ, hball⟩ := hpunc ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, chap9G_zero, dist_self]
    exact hε
  · have hxmem : x ∈ ({0} : Set ℝ)ᶜ := by simpa using hx0
    rw [chap9G_zero]
    exact hball hxmem hx

theorem continuous_chap9G : Continuous chap9G := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · rw [ht]
    exact continuousAt_chap9G_zero
  · have hdiv : ContinuousAt (fun t : ℝ => Real.arcsin t / t) t :=
      Real.continuous_arcsin.continuousAt.div continuousAt_id ht
    have hEq : chap9G =ᶠ[𝓝 t] (fun t : ℝ => Real.arcsin t / t) := by
      filter_upwards [eventually_ne_nhds ht] with s hs
      exact chap9G_of_ne hs
    exact ContinuousAt.congr_of_eventuallyEq hdiv hEq

theorem chap9S_eq_integral_chap9G {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, chap9S u k) = ∫ t in (0 : ℝ)..u, chap9G t := by
  have hcont : ContinuousOn (fun w : ℝ => ∑' k : ℕ, chap9S w k) (Set.Icc 0 u) := by
    apply continuousOn_chap9S_tsum_aux.mono
    intro t ht
    rw [Set.mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2, hu1]
  have hderiv : ∀ t ∈ Set.Ioo 0 u,
      HasDerivAt (fun w : ℝ => ∑' k : ℕ, chap9S w k) (chap9G t) t := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    have habs : |t| < 1 := by
      rw [abs_of_pos ht.1]
      linarith [ht.2, hu1]
    have hS := hasDerivAt_chap9S habs
    have hmul := mul_tsum_Sderiv_eq_arcsin habs
    have htne : t ≠ 0 := ne_of_gt ht.1
    have hval : (∑' k : ℕ, chap9Sderiv t k) = chap9G t := by
      rw [chap9G_of_ne htne, eq_div_iff htne]
      linarith [hmul]
    rwa [hval] at hS
  have hint : IntervalIntegrable chap9G MeasureTheory.volume 0 u :=
    continuous_chap9G.intervalIntegrable 0 u
  have hFTC : (∫ t in (0 : ℝ)..u, chap9G t)
      = (∑' k : ℕ, chap9S u k) - (∑' k : ℕ, chap9S 0 k) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hcont hderiv hint
  rw [chap9S_zero_aux, sub_zero] at hFTC
  exact hFTC.symm

theorem chap9S_one_eq_integral :
    (∑' k : ℕ, chap9S 1 k) = ∫ t in (0 : ℝ)..1, chap9G t :=
  chap9S_eq_integral_chap9G zero_le_one le_rfl

theorem integral_chap9G_eq_integral_h :
    (∫ t in (0 : ℝ)..1, chap9G t)
      = ∫ s in (0 : ℝ)..(Real.pi / 2), chap9G (Real.sin s) * Real.cos s := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt Real.sin (Real.cos x) x := fun x _ => Real.hasDerivAt_sin x
  have hcont : ContinuousOn Real.cos (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  have hg : ContinuousOn chap9G (Real.sin '' Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    continuous_chap9G.continuousOn
  have hsub : (∫ x in (0 : ℝ)..(Real.pi / 2), (chap9G ∘ Real.sin) x * Real.cos x)
      = ∫ x in Real.sin 0..Real.sin (Real.pi / 2), chap9G x :=
    intervalIntegral.integral_comp_mul_deriv' hderiv hcont hg
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  simp only [Function.comp_apply]

theorem sin_mem_Ioo_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.sin θ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hlt : Real.sin θ < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith : -(Real.pi / 2) ≤ θ)
      (le_refl (Real.pi / 2)) h1
    rwa [Real.sin_pi_div_two] at h
  exact ⟨hpos, hlt⟩

theorem abs_sin_lt_one_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Real.sin θ| < 1 := by
  have h := sin_mem_Ioo_pi_half h0 h1
  rw [abs_of_pos h.1]
  exact h.2

theorem arcsin_sin_eq_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.arcsin (Real.sin θ) = θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arcsin_sin (by linarith) (by linarith)

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end
