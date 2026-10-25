import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Borel
open MeasureTheory ProbabilityTheory Real GaussianStability


namespace GaussianStability

/--
[integral_stdGaussian_comp_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean)
-/
@[path]
lemma integral_stdGaussian_comp_coord
  {n : ℕ}
  {n : ℕ}
  {i : Fin n}
  {f : ℝ → ℝ}
-- given
  (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
-- imply
  ∫ x : EuclideanSpace ℝ (Fin n), f (x i) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = ∫ t, f t ∂(gaussianReal 0 1) := by
-- proof
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
    (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  show ∫ v : Fin n → ℝ, f (v i) ∂(Measure.pi (fun _ => gaussianReal 0 1)) = _
  exact integral_comp_eval hf

end GaussianStability

namespace GaussianStability

/--
[sheppard_halfspace_stability_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean)
-/
@[path]
lemma sheppard_halfspace_stability_local
  {n : ℕ}
  {n : ℕ}
  {ρ : ℝ}
-- given
  (hn : 0 < n)
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  gaussianNoiseStability ρ hρ₀ hρ₁ (fun x : EuclideanSpace ℝ (Fin n) => if (0 : ℝ) ≤ x (⟨0, hn⟩ : Fin n) then 1 else -1) = 2 / π * arcsin ρ := by
-- proof
  unfold gaussianNoiseStability gaussianNoiseOperator
  have h_inner : ∀ x : EuclideanSpace ℝ (Fin n),
    (∫ w : EuclideanSpace ℝ (Fin n),
      (if (0:ℝ) ≤ (ρ • x + √(1 - ρ^2) • w) (⟨0, hn⟩ : Fin n) then (1:ℝ) else -1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
    (∫ t : ℝ, (if (0:ℝ) ≤ ρ * (x (⟨0, hn⟩ : Fin n)) + √(1 - ρ^2) * t then (1:ℝ) else -1)
      ∂(gaussianReal 0 1)) := by
    intro x
    have heq : ∀ w : EuclideanSpace ℝ (Fin n),
      (if (0:ℝ) ≤ (ρ • x + √(1 - ρ^2) • w) (⟨0, hn⟩ : Fin n) then (1:ℝ) else -1) =
      (fun t : ℝ => if (0:ℝ) ≤ ρ * (x (⟨0, hn⟩ : Fin n)) + √(1 - ρ^2) * t then (1:ℝ) else -1)
        (w (⟨0, hn⟩ : Fin n)) := fun w => rfl
    simp_rw [heq]
    exact integral_stdGaussian_comp_coord ⟨0, hn⟩ _
      ((measurable_const.ite
        (measurableSet_le measurable_const (measurable_const.add (measurable_const.mul measurable_id)))
        measurable_const).aestronglyMeasurable)
  simp_rw [h_inner]
  have h_outer_asm : AEStronglyMeasurable
    (fun s => (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
      ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1))
    (gaussianReal 0 1) := by
    apply AEStronglyMeasurable.mul
    · exact (measurable_const.ite measurableSet_Ici measurable_const).aestronglyMeasurable
    · apply StronglyMeasurable.aestronglyMeasurable
      apply StronglyMeasurable.integral_prod_right (ν := gaussianReal 0 1)
      apply Measurable.stronglyMeasurable
      exact measurable_const.ite
        (measurableSet_le measurable_const
          ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
        measurable_const
  have h_outer := integral_stdGaussian_comp_coord (n := n) ⟨0, hn⟩
    (fun s => (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
      ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1))
    h_outer_asm
  rw [h_outer]
  have h_eq_sign : (∫ s : ℝ, (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
    ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1)
    ∂(gaussianReal 0 1)) = gaussianNoiseStabilitySign ρ := by
    unfold gaussianNoiseStabilitySign rhoCorrelatedGaussian signFn
    have hmeas_map : Measurable (fun p : ℝ × ℝ => (p.1, ρ * p.1 + √(1 - ρ^2) * p.2)) := by
      fun_prop
    have hf_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (if p.1 ≥ 0 then (1:ℝ) else -1) * (if p.2 ≥ 0 then (1:ℝ) else -1))
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => (p.1, ρ * p.1 + √(1 - ρ^2) * p.2))) :=
      ((measurable_const.ite (measurableSet_Ici.preimage measurable_fst) measurable_const).mul
        (measurable_const.ite (measurableSet_Ici.preimage measurable_snd) measurable_const)).aestronglyMeasurable
    rw [integral_map hmeas_map.aemeasurable hf_meas]
    have h_integrable : Integrable
      (fun p : ℝ × ℝ => (if p.1 ≥ 0 then (1:ℝ) else -1) *
        (if (ρ * p.1 + √(1 - ρ^2) * p.2) ≥ 0 then (1:ℝ) else -1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      apply Integrable.of_bound (C := 1)
      · exact ((measurable_const.ite (measurableSet_Ici.preimage measurable_fst) measurable_const).mul
        (measurable_const.ite (measurableSet_Ici.preimage
          ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
          measurable_const)).aestronglyMeasurable
      · filter_upwards with ⟨s, t⟩
        simp only [Real.norm_eq_abs]
        split_ifs <;> simp [abs_of_pos, abs_of_nonpos]
    rw [integral_prod _ h_integrable]
    congr 1; ext s
    rw [← integral_const_mul]
  rw [h_eq_sign]
  exact sheppard_formula ρ ⟨le_trans (neg_nonpos_of_nonneg zero_le_one) hρ₀, hρ₁⟩

end GaussianStability

namespace GaussianStability

/--
[symmetrize_coord_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean)
-/
@[path]
lemma symmetrize_coord_range
  {n : ℕ}
  {n : ℕ}
  {i : Fin n}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  symmetrize_coord i f x ∈ Set.Icc (-1 : ℝ) 1 := by
-- proof
  unfold symmetrize_coord
  exact thresholdFn_range _ _

end GaussianStability

namespace GaussianStability

/--
[iterateSymmetrize_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean)
-/
@[path]
lemma iterateSymmetrize_range
  {n : ℕ}
  {n : ℕ}
  {k : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
-- given
  (hn : 0 < n)
  (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
-- imply
  ∀ x, iterateSymmetrize hn k f x ∈ Set.Icc (-1 : ℝ) 1 := by
-- proof
  induction k with
  | zero => exact hf_range
  | succ k ih =>
    intro x
    simp only [iterateSymmetrize]
    split_ifs with h
    · exact symmetrize_coord_range _ _ _
    · exact ih x

end GaussianStability

namespace GaussianStability

/--
[iterateSymmetrize_mono_stability](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Borel.lean)
-/
@[path]
lemma iterateSymmetrize_mono_stability
  {n : ℕ}
  {n : ℕ}
  {k : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → ℝ}
  {ρ : ℝ}
-- given
  (hn : 0 < n)
  (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
  (hρ₀ : 0 ≤ ρ)
  (hρ₁ : ρ ≤ 1) :
-- imply
  gaussianNoiseStability ρ hρ₀ hρ₁ f ≤ gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn k f) := by
-- proof
  induction k with
  | zero => simp [iterateSymmetrize]
  | succ k ih =>
    have hk_range := iterateSymmetrize_range hn k f hf_range
    simp only [iterateSymmetrize]
    split_ifs with h
    · calc gaussianNoiseStability ρ hρ₀ hρ₁ f
      ≤ gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn k f) := ih
      _ ≤ gaussianNoiseStability ρ hρ₀ hρ₁
        (symmetrize_coord ⟨k, h⟩ (iterateSymmetrize hn k f)) :=
        coordinate_symmetrization_increases_stability ⟨k, h⟩
          (iterateSymmetrize hn k f) hk_range ρ hρ₀ hρ₁
    · exact ih
end GaussianStability



-- created on 2026-10-23
