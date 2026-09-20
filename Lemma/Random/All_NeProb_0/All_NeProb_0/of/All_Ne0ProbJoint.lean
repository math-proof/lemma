import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.All_EqIntegral_ProbJoint.of.PSpace_Joint
open Random MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.All_NeProb_0.All_NeProb_0.of.All_Ne0ProbJoint |
| And.left | Random.All_NeProb_0.of.All_Ne0ProbJoint.fst |
| And.right | Random.All_NeProb_0.of.All_Ne0ProbJoint.snd |
-/
@[main, And.left, And.right]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  {π : Measure Ω} {x : Ω → α} {y : Ω → β}
-- given
  (hP : PSpace π (x, y))
  (h : ∀ᵐ z ∂(ReferenceMeasure.measure : Measure (α × β)), ℙ[π](x = z.1 ∧ y = z.2) ≠ 0) :
-- imply
  (have := PSpace.of.PSpace_Joint.fst hP; ∀ᵐ «x.bvar» ∂ReferenceMeasure.measure, ℙ[π](x = «x.bvar») ≠ 0) ∧
  (have := PSpace.of.PSpace_Joint.snd hP; ∀ᵐ «y.bvar» ∂ReferenceMeasure.measure, ℙ[π](y = «y.bvar») ≠ 0) := by
-- proof
  extract_lets hP_x hP_y
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  have hpj : Measurable (π.prob (x, y)) := Measure.measurable_rnDeriv _ _
  -- Decompose product a.e. hypothesis into nested forms
  have hae_x : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, π.prob (x, y) (a, b) ≠ 0 := by
    have h' : ∀ᵐ z ∂(μ.prod ν), π.prob (x, y) z ≠ 0 := h
    exact Measure.ae_ae_of_ae_prod h'
  have hae_y : ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, π.prob (x, y) (a, b) ≠ 0 := by
    have hprod : ∀ᵐ z ∂(μ.prod ν), π.prob (x, y) z ≠ 0 := h
    have hswap : ∀ᵐ z ∂(ν.prod μ), π.prob (x, y) (z.2, z.1) ≠ 0 := by
      rw [← Measure.prod_swap] at hprod
      exact ae_of_ae_map measurable_swap.aemeasurable hprod
    exact Measure.ae_ae_of_ae_prod hswap
  -- Section integrals: marginal = ∫ joint
  have hsecx : ∀ᵐ a ∂μ, ∫⁻ b, π.prob (x, y) (a, b) ∂ν = π.prob x a :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint hP
  have hsecy : ∀ᵐ b ∂ν, ∫⁻ a, π.prob (x, y) (a, b) ∂μ = π.prob y b :=
    All_EqIntegral_ProbJoint.of.PSpace_Joint.left hP
  -- Marginal integrals = 1, so reference measures are nonzero
  have hlawx : π.map x = μ.withDensity (π.prob x) := PSpace.map_eq_withDensity_density
  have hlawy : π.map y = ν.withDensity (π.prob y) := PSpace.map_eq_withDensity_density
  have hix : IsProbabilityMeasure (π.map x) :=
    Measure.isProbabilityMeasure_map PSpace.aemeasurable
  have hiy : IsProbabilityMeasure (π.map y) :=
    Measure.isProbabilityMeasure_map PSpace.aemeasurable
  have h1x : ∫⁻ a, π.prob x a ∂μ = 1 := by
    have h : (μ.withDensity (π.prob x)) Set.univ = ∫⁻ a, π.prob x a ∂μ := by
      rw [withDensity_apply (π.prob x) MeasurableSet.univ, setLIntegral_univ]
    rw [← hlawx, measure_univ] at h
    exact h.symm
  have h1y : ∫⁻ b, π.prob y b ∂ν = 1 := by
    have h : (ν.withDensity (π.prob y)) Set.univ = ∫⁻ b, π.prob y b ∂ν := by
      rw [withDensity_apply (π.prob y) MeasurableSet.univ, setLIntegral_univ]
    rw [← hlawy, measure_univ] at h
    exact h.symm
  have hμne : μ ≠ 0 := by
    intro h; rw [h] at h1x; simp [lintegral_zero_measure] at h1x
  have hνne : ν ≠ 0 := by
    intro h; rw [h] at h1y; simp [lintegral_zero_measure] at h1y
  -- Key: for a.e. a (resp. b), section integral is nonzero
  have hkeyx : ∀ᵐ a ∂μ, ∫⁻ b, π.prob (x, y) (a, b) ∂ν ≠ 0 := by
    filter_upwards [hae_x] with a ha
    by_contra hzero
    have hmf : Measurable (fun b ↦ π.prob (x, y) (a, b)) := hpj.comp measurable_prodMk_left
    have hae : ∀ᵐ b ∂ν, π.prob (x, y) (a, b) = 0 :=
      (lintegral_eq_zero_iff hmf).mp hzero
    have hcon : ∀ᵐ b ∂ν, False := by
      filter_upwards [ha, hae] with b hne heq
      exact hne heq
    exact hνne (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hcon))
  have hkeyy : ∀ᵐ b ∂ν, ∫⁻ a, π.prob (x, y) (a, b) ∂μ ≠ 0 := by
    filter_upwards [hae_y] with b hb
    by_contra hzero
    have hmf : Measurable (fun a ↦ π.prob (x, y) (a, b)) := hpj.comp measurable_prodMk_right
    have hae : ∀ᵐ a ∂μ, π.prob (x, y) (a, b) = 0 :=
      (lintegral_eq_zero_iff hmf).mp hzero
    have hcon : ∀ᵐ a ∂μ, False := by
      filter_upwards [hb, hae] with a hne heq
      exact hne heq
    exact hμne (Measure.measure_univ_eq_zero.mp (by simpa using ae_iff.mp hcon))
  have hmainx : ∀ᵐ a ∂μ, π.prob x a ≠ 0 := by
    filter_upwards [hsecx, hkeyx] with a hsec hkey
    rw [← hsec]
    exact hkey
  have hmainy : ∀ᵐ b ∂ν, π.prob y b ≠ 0 := by
    filter_upwards [hsecy, hkeyy] with b hsec hkey
    rw [← hsec]
    exact hkey
  exact ⟨hmainx, hmainy⟩


-- created on 2020-12-08
-- updated on 2026-09-20
