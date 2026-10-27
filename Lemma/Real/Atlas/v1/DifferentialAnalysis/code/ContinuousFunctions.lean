import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
open Set Filter Topology Bornology Metric ContinuousFunctions ContinuousLinearFunctional
open scoped ZeroAtInfty
open Bornology Metric Set


namespace ContinuousFunctions

/--
[continuous_iff_isOpen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma continuous_iff_isOpen_preimage
  [MetricSpace X]
  [MetricSpace Y]
  {f : X → Y} :
-- imply
  List.TFAE [ Continuous f, ∀ O : Set Y, IsOpen O → IsOpen (f ⁻¹' O), ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C), SeqContinuous f ] := by
-- proof
  tfae_have 1 ↔ 2 := continuous_def
  tfae_have 1 ↔ 3 := continuous_iff_isClosed
  tfae_have 1 ↔ 4 := continuous_iff_seqContinuous
  tfae_finish

end ContinuousFunctions

namespace ContinuousFunctions

/--
[decompose_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma decompose_unique
  [TopologicalSpace X]
-- given
  (f g h : C₀(X, ℝ))
  (hdecomp : f = g - h)
  (hg_nonneg : ∀ x, 0 ≤ g x)
  (hh_nonneg : ∀ x, 0 ≤ h x)
  (hg_le : ∀ x, g x ≤ |f x|)
  (hh_le : ∀ x, h x ≤ |f x|) :
-- imply
  g = zeroAtInftyPosPart f ∧ h = zeroAtInftyNegPart f := by
-- proof
  have hfx : ∀ x, f x = g x - h x := fun x => by
    have := DFunLike.congr_fun hdecomp x
    simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply] at this
    exact this
  constructor
  · ext x
    simp only [posPart_apply]
    obtain hle | hgt := le_or_gt (f x) 0
    ·
      rw [max_eq_right hle]
      have hg_abs := hg_le x
      have hh_abs := hh_le x
      rw [abs_of_nonpos hle] at hg_abs hh_abs
      linarith [hg_nonneg x, hh_nonneg x, hfx x]
    ·
      rw [max_eq_left hgt.le]
      have hh_abs := hh_le x
      have hg_abs := hg_le x
      rw [abs_of_pos hgt] at hh_abs hg_abs
      linarith [hh_nonneg x, hfx x]
  · ext x
    simp only [negPart_apply]
    obtain hle | hgt := le_or_gt (f x) 0
    ·
      rw [max_eq_left (by linarith)]
      have hg_abs := hg_le x
      have hh_abs := hh_le x
      rw [abs_of_nonpos hle] at hg_abs hh_abs
      linarith [hg_nonneg x, hh_nonneg x, hfx x]
    ·
      rw [max_eq_right (by linarith)]
      have hh_abs := hh_le x
      have hg_abs := hg_le x
      rw [abs_of_pos hgt] at hh_abs hg_abs
      linarith [hh_nonneg x, hfx x]

end ContinuousFunctions

namespace ContinuousFunctions

/--
[zeroAtInfty_unique_posNeg_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma zeroAtInfty_unique_posNeg_decomposition
  [TopologicalSpace X]
  {f : C₀(X, ℝ)} :
-- imply
  f = zeroAtInftyPosPart f - zeroAtInftyNegPart f ∧ (∀ x, (zeroAtInftyPosPart f) x ≤ |f x|) ∧ (∀ x, (zeroAtInftyNegPart f) x ≤ |f x|) ∧ (∀ g h : C₀(X, ℝ), f = g - h → (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) → (∀ x, g x ≤ |f x|) → (∀ x, h x ≤ |f x|) → g = zeroAtInftyPosPart f ∧ h = zeroAtInftyNegPart f) :=
-- proof
  ⟨decompose_pos_neg f, posPart_le_abs f, negPart_le_abs f, decompose_unique f⟩
end ContinuousFunctions
namespace NormedSpaces


namespace ContinuousLinearFunctional

/--
[continuousAt_zero_of_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma continuousAt_zero_of_continuous
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  {u : V →ₗ[ℝ] ℝ}
-- given
  (h : Continuous u) :
-- imply
  ContinuousAt u 0 :=
-- proof
  h.continuousAt

end ContinuousLinearFunctional

namespace ContinuousLinearFunctional

/--
[bounded_image_closedBall_of_continuousAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma bounded_image_closedBall_of_continuousAt_zero
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  {u : V →ₗ[ℝ] ℝ}
-- given
  (h : ContinuousAt u 0) :
-- imply
  IsBounded (u '' {f : V | ‖f‖ ≤ 1}) := by
-- proof
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h 1 one_pos
  rw [isBounded_iff_forall_norm_le]
  have hδ2_pos : (0 : ℝ) < δ / 2 := half_pos hδ_pos
  refine ⟨(δ / 2)⁻¹, fun y hy => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hy
  simp only [mem_setOf_eq] at hf
  have norm_scaled : ‖(δ / 2) • f‖ < δ := by
    calc ‖(δ / 2) • f‖ = δ / 2 * ‖f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ2_pos]
      _ ≤ δ / 2 * 1 := by gcongr
      _ < δ := by linarith
  have hd : dist (u ((δ / 2) • f)) (u 0) < 1 := hδ (by rwa [dist_zero_right])
  simp only [map_zero, dist_zero_right, map_smul, smul_eq_mul] at hd
  rw [norm_mul, show ‖(δ / 2 : ℝ)‖ = δ / 2 from by
    rw [Real.norm_eq_abs, abs_of_pos hδ2_pos]] at hd
  exact le_of_lt (by rwa [inv_eq_one_div, lt_div_iff₀ hδ2_pos, mul_comm])

end ContinuousLinearFunctional

namespace ContinuousLinearFunctional

/--
[bound_of_bounded_image_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma bound_of_bounded_image_closedBall
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  {u : V →ₗ[ℝ] ℝ}
-- given
  (h : IsBounded (u '' {f : V | ‖f‖ ≤ 1})) :
-- imply
  ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖ := by
-- proof
  rw [isBounded_iff_forall_norm_le] at h
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun f => ?_⟩
  by_cases hf : f = 0
  · simp [hf, map_zero]
  · have hfn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    have normalized_in_ball : ‖f‖⁻¹ • f ∈ {g : V | ‖g‖ ≤ 1} := by
      simp only [mem_setOf_eq, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hfn, le_refl]
    have hbound := hC (u (‖f‖⁻¹ • f)) ⟨‖f‖⁻¹ • f, normalized_in_ball, rfl⟩
    rw [map_smul, smul_eq_mul, norm_mul, norm_inv, norm_norm] at hbound
    calc ‖u f‖ = ‖f‖ * (‖f‖⁻¹ * ‖u f‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hfn, one_mul]
      _ ≤ ‖f‖ * C := by gcongr
      _ = C * ‖f‖ := mul_comm _ _

end ContinuousLinearFunctional

namespace ContinuousLinearFunctional

/--
[continuous_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma continuous_of_bound
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  {u : V →ₗ[ℝ] ℝ}
-- given
  (h : ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖) :
-- imply
  Continuous u := by
-- proof
  obtain ⟨C, hC⟩ := h
  exact AddMonoidHomClass.continuous_of_bound u C hC

end ContinuousLinearFunctional

namespace ContinuousLinearFunctional

/--
[linearFunctional_continuous_tfae](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
lemma linearFunctional_continuous_tfae
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  {u : V →ₗ[ℝ] ℝ} :
-- imply
  List.TFAE [ Continuous u, ContinuousAt u 0, IsBounded (u '' {f : V | ‖f‖ ≤ 1}), ∃ C, ∀ f : V, ‖u f‖ ≤ C * ‖f‖ ] := by
-- proof
  tfae_have 1 → 2 := continuousAt_zero_of_continuous u
  tfae_have 2 → 3 := bounded_image_closedBall_of_continuousAt_zero u
  tfae_have 3 → 4 := bound_of_bounded_image_closedBall u
  tfae_have 4 → 1 := continuous_of_bound u
  tfae_finish

end ContinuousLinearFunctional

/--
[posPart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma posPart_apply_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  zeroAtInftyPosPart f x = max (f x) 0 := by
-- proof
  apply ContinuousFunctions.posPart_apply f x

/--
[negPart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma negPart_apply_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  zeroAtInftyNegPart f x = max (-f x) 0 := by
-- proof
  apply ContinuousFunctions.negPart_apply f x

/--
[decompose_pos_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma decompose_pos_neg_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)} :
-- imply
  f = zeroAtInftyPosPart f - zeroAtInftyNegPart f := by
-- proof
  apply ContinuousFunctions.decompose_pos_neg f

/--
[posPart_le_abs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma posPart_le_abs_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  zeroAtInftyPosPart f x ≤ := by
-- proof
  apply ContinuousFunctions.posPart_le_abs f x

/--
[negPart_le_abs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma negPart_le_abs_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  zeroAtInftyNegPart f x ≤ := by
-- proof
  apply ContinuousFunctions.negPart_le_abs f x

/--
[posPart_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma posPart_nonneg_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  0 ≤ zeroAtInftyPosPart f x := by
-- proof
  apply ContinuousFunctions.posPart_nonneg f x

/--
[negPart_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean)
-/
@[path]
private lemma negPart_nonneg_eq
  [TopologicalSpace X]
  {f : C₀(X, ℝ)}
  {x : X} :
-- imply
  0 ≤ zeroAtInftyNegPart f x := by
-- proof
  apply ContinuousFunctions.negPart_nonneg f x


-- created on 2026-10-23
