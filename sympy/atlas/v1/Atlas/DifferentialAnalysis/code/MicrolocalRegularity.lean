/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary

noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
sphere component `ConicSingularSupportSphere u` is also empty. -/
lemma ConicSingularSupportSphere_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.ConicSingularSupportSphere u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  have hp_norm : ‖w.val‖ = 1 := by
    have := w.property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hp_le : ‖w.val‖ ≤ 1 := le_of_eq hp_norm
  let p : ClosedBall n := ⟨w.val, hp_le⟩
  have hp_mem : p ∈ Css u := by
    show (if h : ‖p.val‖ = 1 then _ else _)
    rw [dif_pos hp_norm]
    convert hw using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
ordinary singular support is also empty. -/
lemma singularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.singularSupport u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have h1x_ne : (1 + ‖x‖ : ℝ) ≠ 0 := ne_of_gt h1x_pos
  set c := (1 + ‖x‖)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr h1x_pos
  have hc_norm : ‖c • x‖ = ‖x‖ / (1 + ‖x‖) := by
    rw [norm_smul, Real.norm_of_nonneg hc_pos.le, hc_def, inv_mul_eq_div]
  have hc_lt : ‖c • x‖ < 1 := by
    rw [hc_norm]
    rw [div_lt_one h1x_pos, lt_add_iff_pos_left]
    exact one_pos
  have hc_le : ‖c • x‖ ≤ 1 := le_of_lt hc_lt
  let p : ClosedBall n := ⟨c • x, hc_le⟩
  have hp_ne : ‖p.val‖ ≠ 1 := ne_of_lt hc_lt
  have hto : p.toEuclidean hc_lt = x := by
    simp only [ClosedBall.toEuclidean, p]
    rw [hc_norm]
    have h_factor : (1 : ℝ) - ‖x‖ / (1 + ‖x‖) = 1 / (1 + ‖x‖) := by
      field_simp
      ring
    rw [h_factor, one_div, inv_inv, smul_smul]
    rw [hc_def, mul_inv_cancel₀ h1x_ne, one_smul]
  have hp_mem : p ∈ Css u := by
    show (if hh : ‖p.val‖ = 1 then _ else _)
    rw [dif_neg hp_ne]
    convert hx using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
cone singular support (the union of singular support and conic sphere part) is also empty. -/
lemma coneSingularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.coneSingularSupport u = ∅ := by
  simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff, Set.image_eq_empty]
  exact ⟨singularSupport_empty_of_Css_empty u h,
    ConicSingularSupportSphere_empty_of_Css_empty u h⟩

/-- When the conic singular support `Css u` of a tempered distribution is empty, produce a Schwartz
function whose Schwartz embedding equals `u`. -/
def toSchwartzOfEmptyCss {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  ((ConeSupport.coneSingularSupport_eq_empty_iff u).mp
    (coneSingularSupport_empty_of_Css_empty u h)).choose

/-- Predicate that `ψ₁` acts as a conic cutoff separating conic singular supports `K₁` and `K₂`:
multiplying by `ψ₁` (resp. `1 - ψ₁`) kills the conic singular support of any distribution whose
`Css` lies in `K₂` (resp. `K₁`). -/
structure IsConicCutoffForDisjointCss (K₁ K₂ : Set (ClosedBall n))
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop where
  schwartz_of_mul :
    ∀ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₂ ⊆ K₂ →
      Css (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂) = ∅
  schwartz_of_compl_mul :
    ∀ u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₁ ⊆ K₁ →
      Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) = ∅

/-- Pairing of distributions `u₁, u₂` with disjoint conic singular supports, defined via a
specified conic cutoff `ψ₁`: applies `u₁` to the Schwartz representative of `ψ₁ · u₂` and `u₂` to
the Schwartz representative of `(1 - ψ₁) · u₁`, then sums. -/
def cssPairingWith {K₁ K₂ : Set (ClosedBall n)}
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) : ℂ :=
  u₁ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂)) +
  u₂ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁))
