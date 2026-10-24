/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SmoothVectorsProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import sympy.atlas.v1.Atlas.LieGroups.code.KFinite
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section

open scoped Manifold
open MeasureTheory

namespace ContinuousRep

section GStable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

end GStable

section Subspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [MeasureSpace G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def repOfFunction (π : ContinuousRep G F) (f : G → ℂ) (v : F) : F :=
  ∫ g, (f g) • ((π.toMonoidHom g) v)

def IsSmoothCompactlySupportedFunction (f : G → ℂ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f

def gardingSubspace (π : ContinuousRep G F) : Submodule ℂ F :=
  Submodule.span ℂ
    { w : F | ∃ (f : G → ℂ) (v : F),
        IsSmoothCompactlySupportedFunction I f ∧ w = π.repOfFunction f v }

def leftInvariantDeriv (lieExp : E → G) (X : E) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => f (g * lieExp (t • X))) 0

end Subspace

section Garding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [MeasureSpace G] [CompleteSpace F]
variable [FiniteDimensional ℝ E] [T2Space G]
variable [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)]
variable [BorelSpace G]
variable [SecondCountableTopology G] [LocallyCompactSpace G]

/-- Chart-coordinate smoothness of the Lie-group convolution. Upstream atlas-lean
leaves the analytic core as `sorry`; keep the same surface so dependent theorems
typecheck and export oleans for Bijective / Complex SmoothVectors. -/
theorem contDiffOn_convolution_chartCoord
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) (x₀ : G) :
    ContDiffOn ℝ ↑(⊤ : ℕ∞)
      (fun x => ∫ g, (f (((extChartAt I x₀).symm x)⁻¹ * g)) • w g)
      (extChartAt I x₀).target := by
  sorry

theorem contMDiff_convolution_integral
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun h => ∫ g, (f (h⁻¹ * g)) • w g) := by
  intro h₀
  rw [contMDiffAt_iff]
  set φ := fun x => ∫ g, (f (((extChartAt I h₀).symm x)⁻¹ * g)) • w g with hφ_def
  have hsmooth := contDiffOn_convolution_chartCoord I f hf w h₀
  have hmem_src : h₀ ∈ (extChartAt I h₀).source := mem_extChartAt_source h₀
  have hmem_tgt : (extChartAt I h₀) h₀ ∈ (extChartAt I h₀).target :=
    (extChartAt I h₀).map_source hmem_src
  have heq : ∀ x ∈ (extChartAt I h₀).source,
      (fun h => ∫ g, (f (h⁻¹ * g)) • w g) x = φ ((extChartAt I h₀) x) := by
    intro x hx
    simp only [hφ_def, (extChartAt I h₀).left_inv hx]
  have hcont_φ := hsmooth.continuousOn
  constructor
  · have hcont_comp : ContinuousOn (φ ∘ (extChartAt I h₀)) (extChartAt I h₀).source := by
      apply hcont_φ.comp (continuousOn_extChartAt h₀)
      intro x hx; exact (extChartAt I h₀).map_source hx
    have hcont_on_src : ContinuousOn (fun h => ∫ g, (f (h⁻¹ * g)) • w g)
        (extChartAt I h₀).source := by
      apply hcont_comp.congr
      intro x hx
      exact heq x hx
    exact hcont_on_src.continuousAt ((isOpen_extChartAt_source h₀).mem_nhds hmem_src)
  · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe]
    exact (hsmooth.contDiffWithinAt hmem_tgt).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin h₀)

theorem continuous_lieGroup_convolution
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) :
    Continuous (fun h => ∫ g, (f (h⁻¹ * g)) • w g) :=
  (contMDiff_convolution_integral I f hf w).continuous

omit [T2Space G] [BorelSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] in
theorem orbitMap_gardingVector_eq
    (π : ContinuousRep G F) (f : G → ℂ) (v : F) (h : G)
    (hint : Integrable (fun g => f g • (π.toMonoidHom g) v)) :
    π.orbitMap (π.repOfFunction f v) h =
      ∫ g, (f (h⁻¹ * g)) • ((π.toMonoidHom g) v) := by
  simp only [orbitMap, repOfFunction]
  have h1 := (ContinuousLinearMap.integral_comp_comm (π.toMonoidHom h) hint).symm
  rw [h1]
  simp_rw [ContinuousLinearMap.map_smul]
  simp_rw [← mul_apply_eq_comp, ← map_mul π.toMonoidHom]
  have h4 : (fun g => f g • (π.toMonoidHom (h * g)) v) =
      (fun g => f (h⁻¹ * g) • (π.toMonoidHom g) v) ∘ (fun g => h * g) := by
    ext g; simp
  rw [h4]; simp only [Function.comp_def]
  exact @MeasureTheory.integral_mul_left_eq_self G F _ _ _ (volume : Measure G) _ _ _
    (fun g => f (h⁻¹ * g) • (π.toMonoidHom g) v) h

theorem gardingVector_isSmooth
    (π : ContinuousRep G F) (f : G → ℂ)
    (hf : IsSmoothCompactlySupportedFunction I f)
    (v : F) :
    π.IsSmoothVector I (π.repOfFunction f v) := by
  show ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap (π.repOfFunction f v))
  by_cases hint : Integrable (fun g => f g • (π.toMonoidHom g) v)
  · have heq : π.orbitMap (π.repOfFunction f v) =
        fun h => ∫ g, (f (h⁻¹ * g)) • ((π.toMonoidHom g) v) := by
      ext h; exact orbitMap_gardingVector_eq π f v h hint
    rw [heq]
    exact contMDiff_convolution_integral I f hf (fun g => (π.toMonoidHom g) v)
  · have h0 : π.repOfFunction f v = 0 := by
      simp only [repOfFunction]
      exact integral_undef hint
    rw [h0]
    show ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap 0)
    have : π.orbitMap 0 = fun _ => (0 : F) := by
      ext g; simp [orbitMap]
    rw [this]
    exact contMDiff_const

omit [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)] in
theorem exists_smooth_dirac_sequence
    [Measure.IsHaarMeasure (volume : Measure G)] :
    ∃ (φ : ℕ → G → ℂ),
      (∀ n, IsSmoothCompactlySupportedFunction I (φ n)) ∧
      (∀ n, ∀ g, (φ n g).im = 0 ∧ 0 ≤ (φ n g).re) ∧
      (∀ n, ∫ g, (φ n g).re = 1) ∧
      (∀ U ∈ nhds (1 : G), ∃ N, ∀ n, N ≤ n → Function.support (φ n) ⊆ U) := by
  have hmanif : IsManifold I (↑(⊤ : ℕ∞)) G := IsManifold.of_le le_top
  have hbasis := SmoothBumpFunction.nhds_basis_tsupport (I := I) (1 : G)
  obtain ⟨ψ, _, hanti⟩ := hbasis.exists_antitone_subbasis
  have hint_pos : ∀ n, 0 < ∫ g, (ψ n : G → ℝ) g := by
    intro n
    exact integral_pos_of_integrable_nonneg_nonzero
      (ψ n).contMDiff.continuous
      ((ψ n).contMDiff.continuous.integrable_of_hasCompactSupport (ψ n).hasCompactSupport)
      (fun g => (ψ n).nonneg)
      (by rw [(ψ n).eq_one]; exact one_ne_zero)
  refine ⟨fun n g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ), ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · show ContMDiff I 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ))
      have heq : (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ)) =
          Complex.ofRealCLM ∘ (fun g => (∫ x, (ψ n : G → ℝ) x)⁻¹ * ψ n g) := by
        ext g; simp [mul_comm]
      rw [heq]
      have h_inner : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
          (fun g => (∫ x, (ψ n : G → ℝ) x)⁻¹ * (ψ n : G → ℝ) g) := by
        have hc : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
            (fun _ : G => (∫ x, (ψ n : G → ℝ) x)⁻¹) := contMDiff_const
        exact hc.mul (ψ n).contMDiff
      have h_ofReal : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) Complex.ofRealCLM :=
        Complex.ofRealCLM.contMDiff.of_le le_top
      exact h_ofReal.comp h_inner
    · show HasCompactSupport (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ))
      apply HasCompactSupport.of_support_subset_isCompact (ψ n).hasCompactSupport.isCompact
      intro g hg
      rw [Function.mem_support] at hg
      apply subset_closure
      rw [Function.mem_support]
      intro h
      apply hg
      simp [h]
  · intro n g
    constructor
    · show (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).im = 0
      exact Complex.ofReal_im _
    · show 0 ≤ (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).re
      rw [Complex.ofReal_re]
      exact mul_nonneg (ψ n).nonneg (le_of_lt (inv_pos.mpr (hint_pos n)))
  · intro n
    show ∫ g, (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).re = 1
    simp_rw [Complex.ofReal_re]
    rw [integral_mul_const]
    rw [mul_inv_cancel₀]
    exact ne_of_gt (hint_pos n)
  · intro U hU
    obtain ⟨N, _, hN⟩ := hanti.toHasBasis.mem_iff.mp hU
    refine ⟨N, fun n hn g hg => ?_⟩
    apply hN
    apply hanti.antitone hn
    rw [Function.mem_support] at hg
    apply subset_closure
    rw [Function.mem_support]
    intro h; apply hg; simp [h]

omit [LieGroup I ⊤ G] [FiniteDimensional ℝ E] [MeasurableMul G]
  [Measure.IsMulLeftInvariant (volume : Measure G)] in
theorem smooth_dirac_convolution_tendsto
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)]
    (v : F)
    (φ : ℕ → G → ℂ)
    (hφsmooth : ∀ n, IsSmoothCompactlySupportedFunction I (φ n))
    (hφnonneg : ∀ n, ∀ g, (φ n g).im = 0 ∧ 0 ≤ (φ n g).re)
    (hφnorm : ∀ n, ∫ g, (φ n g).re = 1)
    (hφshrink : ∀ U ∈ nhds (1 : G), ∃ N, ∀ n, N ≤ n → Function.support (φ n) ⊆ U) :
    Filter.Tendsto (fun n => π.repOfFunction (φ n) v) Filter.atTop (nhds v) := by
  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε
  have hcont_action : Continuous (fun g : G => (π.toMonoidHom g) v) :=
    π.continuous_action.comp (continuous_id.prodMk continuous_const)
  have hpi1 : (π.toMonoidHom 1) v = v := by
    rw [MonoidHom.map_one]; exact one_apply_eq_self v
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have hU : {g : G | ‖(π.toMonoidHom g) v - v‖ < ε / 2} ∈ nhds (1 : G) := by
    have hcont : ContinuousAt (fun g : G => ‖(π.toMonoidHom g) v - v‖) (1 : G) :=
      continuous_norm.continuousAt.comp (hcont_action.sub continuous_const).continuousAt
    have hnorm0 : ‖(π.toMonoidHom (1 : G)) v - v‖ = 0 := by simp [map_one]
    have hset : {g : G | ‖(π.toMonoidHom g) v - v‖ < ε / 2} =
        Set.preimage (fun g : G => ‖(π.toMonoidHom g) v - v‖) (Set.Iio (ε / 2)) := rfl
    rw [hset]
    exact hcont.preimage_mem_nhds (by simpa [hnorm0] using Iio_mem_nhds hε2)
  obtain ⟨N, hN⟩ := hφshrink _ hU
  refine ⟨N, fun n hn => ?_⟩
  have hφreal : ∀ g, φ n g = ((φ n g).re : ℂ) := by
    intro g; apply Complex.ext <;> simp [(hφnonneg n g).1]
  have hφnorm_eq : ∀ g, ‖φ n g‖ = (φ n g).re := by
    intro g; conv_lhs => rw [hφreal g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφnonneg n g).2]
  have hφint_one : ∫ g, φ n g = (1 : ℂ) := by
    have heq : (fun g => φ n g) = fun g => ((φ n g).re : ℂ) := funext hφreal
    rw [heq, integral_complex_ofReal, hφnorm n]; simp
  have hφcont : Continuous (φ n) := (hφsmooth n).1.continuous
  have hφsupp : HasCompactSupport (φ n) := (hφsmooth n).2
  have hint1 : MeasureTheory.Integrable (fun g => (φ n g) • ((π.toMonoidHom g) v)) :=
    hcont_action.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφcont hφsupp
  have hint2 : MeasureTheory.Integrable (fun g => (φ n g) • v) :=
    continuous_const.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφcont hφsupp
  have hv_eq : v = ∫ g, (φ n g) • v := by
    rw [integral_smul_const]; erw [hφint_one]; simp
  have hkey : π.repOfFunction (φ n) v - v = ∫ g, (φ n g) • ((π.toMonoidHom g) v - v) := by
    have hsub : (∫ g, (φ n g) • ((π.toMonoidHom g) v)) - (∫ g, (φ n g) • v)
        = ∫ g, (φ n g) • ((π.toMonoidHom g) v - v) := by
      rw [← MeasureTheory.integral_sub hint1 hint2]
      congr 1; ext g; rw [smul_sub]
    simp only [repOfFunction]
    rw [← hsub]
    congr 1
  rw [hkey]
  have hint_re : MeasureTheory.Integrable (fun g => (φ n g).re) := by
    apply (Complex.continuous_re.comp hφcont).integrable_of_hasCompactSupport
    exact hφsupp.comp_left (show Complex.re 0 = 0 from rfl)
  calc ‖∫ g, (φ n g) • ((π.toMonoidHom g) v - v)‖
      ≤ ∫ g, ‖(φ n g) • ((π.toMonoidHom g) v - v)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ g, ‖φ n g‖ * ‖(π.toMonoidHom g) v - v‖ := by
        congr 1; ext g; exact norm_smul _ _
    _ ≤ ∫ g, (φ n g).re * (ε / 2) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun g => by positivity)
        · exact hint_re.mul_const (ε / 2)
        · apply Filter.Eventually.of_forall; intro g
          show ‖φ n g‖ * ‖(π.toMonoidHom g) v - v‖ ≤ (φ n g).re * (ε / 2)
          rw [hφnorm_eq g]
          by_cases hg : g ∈ Function.support (φ n)
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hN n hn hg)) (hφnonneg n g).2
          · rw [Function.mem_support, not_not] at hg; simp [hg]
    _ = (ε / 2) * ∫ g, (φ n g).re := by
        rw [MeasureTheory.integral_mul_const]; ring
    _ = (ε / 2) * 1 := by rw [hφnorm n]
    _ = ε / 2 := mul_one _
    _ < ε := half_lt_self hε

omit [MeasurableMul G]
  [Measure.IsMulLeftInvariant (volume : Measure G)] in
theorem exists_gardingVector_tendsto
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)]
    (v : F) :
    ∃ (φ : ℕ → G → ℂ),
      (∀ n, IsSmoothCompactlySupportedFunction I (φ n)) ∧
      Filter.Tendsto (fun n => π.repOfFunction (φ n) v) Filter.atTop (nhds v) := by
  obtain ⟨φ, hφsmooth, hφnonneg, hφnorm, hφshrink⟩ :=
    exists_smooth_dirac_sequence (G := G) I
  exact ⟨φ, hφsmooth,
    smooth_dirac_convolution_tendsto I π v φ hφsmooth hφnonneg hφnorm hφshrink⟩

omit [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)] in
theorem gardingSubspace_dense
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)] :
    Dense (π.gardingSubspace I : Set F) := by
  rw [Dense]
  intro v
  obtain ⟨φ, hφsmooth, hφconv⟩ := exists_gardingVector_tendsto I π v
  have hmem : ∀ n, π.repOfFunction (φ n) v ∈ (π.gardingSubspace I : Set F) := by
    intro n
    apply Submodule.subset_span
    exact ⟨φ n, v, hφsmooth n, rfl⟩
  exact mem_closure_of_tendsto hφconv (Filter.Eventually.of_forall hmem)

end Garding

section FiniteSubsetSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

end FiniteSubsetSmooth

end ContinuousRep

end
