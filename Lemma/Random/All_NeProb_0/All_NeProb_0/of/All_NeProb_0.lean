import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
open Random MeasureTheory


@[main, And.left, And.right]
private lemma main
  {Ω α β : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace 𝕡 (x, y))
  (h : ∀ᵐ z ∂ReferenceMeasure.measure, 𝕡.prob (x, y) z ≠ 0) :
-- imply
  (have := PSpace.of.PSpace_Joint.fst hP; ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, 𝕡.prob x «x.bvar» ≠ 0) ∧
  (have := PSpace.of.PSpace_Joint.snd hP; ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure, 𝕡.prob y «y.bvar» ≠ 0) := by
-- proof
  extract_lets hP_x hP_y
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hpj : Measurable (𝕡.prob (x, y)) := Measure.measurable_rnDeriv _ _
  -- Decompose product a.e. hypothesis into nested forms
  have hae_x : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, 𝕡.prob (x, y) (a, b) ≠ 0 := by
    have h' : ∀ᵐ z ∂(μ.prod ν), 𝕡.prob (x, y) z ≠ 0 := h
    exact Measure.ae_ae_of_ae_prod h'
  have hae_y : ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, 𝕡.prob (x, y) (a, b) ≠ 0 := by
    have hprod : ∀ᵐ z ∂(μ.prod ν), 𝕡.prob (x, y) z ≠ 0 := h
    have hswap : ∀ᵐ z ∂(ν.prod μ), 𝕡.prob (x, y) (z.2, z.1) ≠ 0 := by
      rw [← Measure.prod_swap] at hprod
      exact ae_of_ae_map measurable_swap.aemeasurable hprod
    exact Measure.ae_ae_of_ae_prod hswap
  -- Section integrals: marginal = ∫ joint
  have hsecx : ∀ᵐ a ∂μ, ∫⁻ b, 𝕡.prob (x, y) (a, b) ∂ν = 𝕡.prob x a :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint hP
  have hsecy : ∀ᵐ b ∂ν, ∫⁻ a, 𝕡.prob (x, y) (a, b) ∂μ = 𝕡.prob y b :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint.left hP
  -- Marginal integrals = 1, so reference measures are nonzero
  have hlawx : 𝕡.map x = μ.withDensity (𝕡.prob x) := PSpace.map_eq_withDensity_density
  have hlawy : 𝕡.map y = ν.withDensity (𝕡.prob y) := PSpace.map_eq_withDensity_density
  have hix : IsProbabilityMeasure (𝕡.map x) :=
    Measure.isProbabilityMeasure_map PSpace.aemeasurable
  have hiy : IsProbabilityMeasure (𝕡.map y) :=
    Measure.isProbabilityMeasure_map PSpace.aemeasurable
  have h1x : ∫⁻ a, 𝕡.prob x a ∂μ = 1 := by
    have h : (μ.withDensity (𝕡.prob x)) Set.univ = ∫⁻ a, 𝕡.prob x a ∂μ := by
      rw [withDensity_apply (𝕡.prob x) MeasurableSet.univ, setLIntegral_univ]
    rw [← hlawx, measure_univ] at h
    exact h.symm
  have h1y : ∫⁻ b, 𝕡.prob y b ∂ν = 1 := by
    have h : (ν.withDensity (𝕡.prob y)) Set.univ = ∫⁻ b, 𝕡.prob y b ∂ν := by
      rw [withDensity_apply (𝕡.prob y) MeasurableSet.univ, setLIntegral_univ]
    rw [← hlawy, measure_univ] at h
    exact h.symm
  have hμne : μ ≠ 0 := by
    intro h; rw [h] at h1x; simp [lintegral_zero_measure] at h1x
  have hνne : ν ≠ 0 := by
    intro h; rw [h] at h1y; simp [lintegral_zero_measure] at h1y
  -- Key: for a.e. a (resp. b), section integral is nonzero
  have hkeyx : ∀ᵐ a ∂μ, ∫⁻ b, 𝕡.prob (x, y) (a, b) ∂ν ≠ 0 := by
    filter_upwards [hae_x] with a ha
    by_contra hzero
    have hmf : Measurable (fun b ↦ 𝕡.prob (x, y) (a, b)) := hpj.comp measurable_prodMk_left
    have hae : ∀ᵐ b ∂ν, 𝕡.prob (x, y) (a, b) = 0 :=
      (lintegral_eq_zero_iff hmf).mp hzero
    have hcon : ∀ᵐ b ∂ν, False := by
      filter_upwards [ha, hae] with b hne heq
      exact hne heq
    exact hνne (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hcon))
  have hkeyy : ∀ᵐ b ∂ν, ∫⁻ a, 𝕡.prob (x, y) (a, b) ∂μ ≠ 0 := by
    filter_upwards [hae_y] with b hb
    by_contra hzero
    have hmf : Measurable (fun a ↦ 𝕡.prob (x, y) (a, b)) := hpj.comp measurable_prodMk_right
    have hae : ∀ᵐ a ∂μ, 𝕡.prob (x, y) (a, b) = 0 :=
      (lintegral_eq_zero_iff hmf).mp hzero
    have hcon : ∀ᵐ a ∂μ, False := by
      filter_upwards [hb, hae] with a hne heq
      exact hne heq
    exact hμne (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hcon))
  have hmainx : ∀ᵐ a ∂μ, 𝕡.prob x a ≠ 0 := by
    filter_upwards [hsecx, hkeyx] with a hsec hkey
    rw [← hsec]
    exact hkey
  have hmainy : ∀ᵐ b ∂ν, 𝕡.prob y b ≠ 0 := by
    filter_upwards [hsecy, hkeyy] with b hsec hkey
    rw [← hsec]
    exact hkey
  exact ⟨hmainx, hmainy⟩


-- created on 2020-12-08
-- updated on 2026-09-14
