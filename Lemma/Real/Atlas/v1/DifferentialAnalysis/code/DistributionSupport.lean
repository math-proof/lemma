import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.DistributionSupport
open Distribution SchwartzMap TemperedDistribution
open scoped SchwartzMap
open sets on which `u` vanishes, applies a Schwartz partition of unity to


namespace SchwartzMap

/--
[compactlySupportedDense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionSupport.lean)
-/
@[path]
lemma compactlySupportedDense
  [NormedAddCommGroup E]
  [NormedSpace ℝ E] :
-- imply
  Dense {φ : 𝓢(E, ℂ) | HasCompactSupport φ} := by
-- proof
  intro f
  apply mem_closure_of_tendsto (f := fun m => bumpCutoffMul m f) (b := Filter.atTop)
  ·
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ f]
    intro ⟨k, j⟩ ε hε
    have h := seminorm_cutoff_sub_tendsto ℂ f k j
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [Filter.Ici_mem_atTop N] with m hm
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    have h1 := hN m hm
    rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h1
    calc (SchwartzMap.seminorm ℂ k j) (bumpCutoffMul m f - f)
      = (SchwartzMap.seminorm ℂ k j) (f - bumpCutoffMul m f) := by
        rw [← map_neg_eq_map]; congr 1; abel
      _ < ε := h1
  ·
    exact Filter.Eventually.of_forall (fun m => bumpCutoffMul_hasCompactSupport m f)
end SchwartzMap


namespace TemperedDistribution

/--
[compactly_supported_dense_in_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionSupport.lean)
-/
@[path]
lemma compactly_supported_dense_in_schwartz
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, F)}
  {ψ : 𝓢(E, ℂ)}
-- given
  (h : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ → u φ = 0) :
-- imply
  u ψ = 0 := by
-- proof
  have hclosed : IsClosed {φ : 𝓢(E, ℂ) | u φ = 0} :=
    isClosed_eq u.cont continuous_const
  have hsub : {φ : 𝓢(E, ℂ) | HasCompactSupport φ} ⊆ {φ : 𝓢(E, ℂ) | u φ = 0} :=
    fun φ hφ => h φ hφ
  have hdense : Dense {φ : 𝓢(E, ℂ) | HasCompactSupport φ} :=
    SchwartzMap.compactlySupportedDense
  have hcl : closure {φ : 𝓢(E, ℂ) | HasCompactSupport φ} ⊆ {φ : 𝓢(E, ℂ) | u φ = 0} :=
    closure_minimal hsub hclosed
  have hψ : ψ ∈ closure {φ : 𝓢(E, ℂ) | HasCompactSupport φ} := by
    rw [hdense.closure_eq]
    exact Set.mem_univ ψ
  exact hcl hψ

end TemperedDistribution

namespace TemperedDistribution

/--
[eq_zero_of_dsupport_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionSupport.lean)
-/
@[path]
lemma eq_zero_of_dsupport_eq_empty
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, F)}
-- given
  (hu : dsupport u = ∅) :
-- imply
  u = 0 := by
-- proof
  have h_local : ∀ x : E, ∃ s : Set E, IsVanishingOn (⇑u) s ∧ IsOpen s ∧ x ∈ s := by
    intro x
    have : x ∉ dsupport u := by simp [hu]
    rwa [notMem_dsupport_iff] at this
  have h_compact : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ → u φ = 0 :=
    fun φ hφ => schwartz_partition_of_unity_vanishing u h_local φ hφ
  ext ψ
  show u ψ = 0
  exact compactly_supported_dense_in_schwartz u ψ h_compact
end TemperedDistribution



-- created on 2026-10-23
