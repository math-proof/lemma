import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.Sheppard
open MeasureTheory ProbabilityTheory Real GaussianStability


namespace GaussianStability

/--
[sheppard_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Sheppard.lean)
-/
@[path]
lemma sheppard_formula
  {ρ : ℝ}
-- given
  (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) :
-- imply
  gaussianNoiseStabilitySign ρ = (2 / π) * Real.arcsin ρ := by
-- proof
  have hkey : gaussianNoiseStabilitySign ρ = BooleanFourier.gaussianSignCorrelation ρ := by
    simp only [gaussianNoiseStabilitySign, BooleanFourier.gaussianSignCorrelation,
      signFn, BooleanFourier.signFn]
  obtain ⟨hρ_lb, hρ_ub⟩ := hρ
  obtain h_neg1 | hρ_gt := eq_or_lt_of_le hρ_lb
  ·
    subst h_neg1
    simp only [neg_neg] at hkey
    rw [hkey]
    simp only [Real.arcsin_neg_one]
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    rw [show (2 : ℝ) / π * -(π / 2) = -1 from by field_simp]
    show BooleanFourier.gaussianSignCorrelation (-1) = -1
    unfold BooleanFourier.gaussianSignCorrelation
    have hmap_eq : (fun p : ℝ × ℝ => (p.1, (-1:ℝ) * p.1 + Real.sqrt (1 - (-1) ^ 2) * p.2)) =
      (fun p : ℝ × ℝ => (p.1, -p.1)) := by
      ext ⟨x, z⟩ <;> simp [Real.sqrt_zero]
    simp only [rhoCorrelatedGaussian, hmap_eq]
    have hmeas : Measurable (fun p : ℝ × ℝ => (p.1, -p.1)) := by fun_prop
    have hf_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => BooleanFourier.signFn p.1 * BooleanFourier.signFn p.2)
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (p.1, -p.1))) := by
      apply AEStronglyMeasurable.mul
      · exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp
        measurable_fst |>.aestronglyMeasurable
      · exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp
        measurable_snd |>.aestronglyMeasurable
    rw [integral_map hmeas.aemeasurable hf_meas]
    have h_ae : (fun p : ℝ × ℝ => BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, -q.1)) p).1 *
      BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, -q.1)) p).2) =ᵐ[(gaussianReal 0 1).prod (gaussianReal 0 1)] fun _ => (-1 : ℝ) := by
      rw [Filter.EventuallyEq, ae_iff]
      apply le_antisymm _ (zero_le _)
      calc ((gaussianReal 0 1).prod (gaussianReal 0 1))
        {p | BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, -q.1)) p).1 *
          BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, -q.1)) p).2 ≠ -1}
        ≤ ((gaussianReal 0 1).prod (gaussianReal 0 1)) ({0} ×ˢ Set.univ) := by
          apply measure_mono
          intro ⟨x, z⟩ hxz
          simp only [BooleanFourier.signFn, Set.mem_setOf_eq] at hxz
          simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
          by_contra hne
          apply hxz
          by_cases hge : x ≥ 0
          · have hpos : x > 0 := lt_of_le_of_ne hge (Ne.symm hne)
            have : ¬ (-x ≥ 0) := by linarith
            simp [hge, this]
          · have : -x > 0 := by linarith
            simp [hge, le_of_lt this]
        _ = (gaussianReal 0 1) {0} * (gaussianReal 0 1) Set.univ := Measure.prod_prod _ _
        _ = 0 := by
          haveI : NoAtoms (gaussianReal (0:ℝ) 1) := noAtoms_gaussianReal one_ne_zero
          simp [measure_singleton]
    rw [integral_congr_ae h_ae, integral_const]; simp
  · rcases eq_or_lt_of_le hρ_ub with h_pos1 | hρ_lt
    ·
      subst h_pos1
      rw [hkey]
      simp only [Real.arcsin_one]
      have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
      rw [show (2 : ℝ) / π * (π / 2) = 1 from by field_simp]
      show BooleanFourier.gaussianSignCorrelation 1 = 1
      unfold BooleanFourier.gaussianSignCorrelation
      have hmap_eq : (fun p : ℝ × ℝ => (p.1, (1:ℝ) * p.1 + Real.sqrt (1 - 1 ^ 2) * p.2)) =
        (fun p : ℝ × ℝ => (p.1, p.1)) := by
        ext ⟨x, z⟩ <;> simp [Real.sqrt_zero]
      simp only [rhoCorrelatedGaussian, hmap_eq]
      have hmeas : Measurable (fun p : ℝ × ℝ => (p.1, p.1)) := by fun_prop
      have hf_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => BooleanFourier.signFn p.1 * BooleanFourier.signFn p.2)
        (((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (p.1, p.1))) := by
        apply AEStronglyMeasurable.mul
        · exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp
          measurable_fst |>.aestronglyMeasurable
        · exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp
          measurable_snd |>.aestronglyMeasurable
      rw [integral_map hmeas.aemeasurable hf_meas]
      have h_eq : (fun p : ℝ × ℝ => BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, q.1)) p).1 *
        BooleanFourier.signFn ((fun q : ℝ × ℝ => (q.1, q.1)) p).2) = fun _ => (1 : ℝ) := by
        ext ⟨x, _⟩; simp only [BooleanFourier.signFn]; split_ifs <;> ring
      rw [h_eq, integral_const]; simp
    ·
      rw [hkey]
      exact BooleanFourier.sheppard_formula_local ρ hρ_gt hρ_lt

end GaussianStability

namespace GaussianStability

/--
[sheppard_formula_arccos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Sheppard.lean)
-/
@[path]
lemma sheppard_formula_arccos
  {ρ : ℝ}
-- given
  (hρ_gt : -1 < ρ)
  (hρ_lt : ρ < 1) :
-- imply
  Filter.Tendsto (fun k => BooleanFourier.noiseStability ρ (BooleanFourier.majorityFn (2 * k + 1))) Filter.atTop (nhds (1 - 2 / Real.pi * Real.arccos ρ)) := by
-- proof
  have h := BooleanFourier.noiseStability_majority_tendsto ρ hρ_gt hρ_lt
  suffices heq : (2 : ℝ) / Real.pi * Real.arcsin ρ = 1 - 2 / Real.pi * Real.arccos ρ by
    rwa [heq] at h
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp
  ring
end GaussianStability



-- created on 2026-10-23
