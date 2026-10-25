import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzComplete
open Filter Topology SchwartzMap
open scoped SchwartzMap


/--
[cauchySeq_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
lemma cauchySeq_seminorm
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {u : ℕ → 𝓢(E, F)}
  {k n : ℕ}
  {ε : ℝ}
-- given
  (hu : CauchySeq u)
  (hε : 0 < ε) :
-- imply
  ∃ N, ∀ m l, N ≤ m → N ≤ l → SchwartzMap.seminorm ℝ k n (u m - u l) < ε := by
-- proof
  rw [cauchySeq_iff_tendsto] at hu
  rw [uniformity_eq_comap_nhds_zero] at hu
  rw [Filter.tendsto_comap_iff] at hu
  have hws := schwartz_withSeminorms ℝ E F
  have hcont := hws.continuous_seminorm (k, n)
  have hball : (SchwartzMap.seminorm ℝ k n).ball 0 ε ∈ 𝓝 (0 : 𝓢(E, F)) :=
    Seminorm.ball_mem_nhds hcont hε
  have hmem := hu hball
  rw [Filter.mem_map, Filter.mem_atTop_sets] at hmem
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := hmem
  refine ⟨max N₁ N₂, fun m l hm hl => ?_⟩
  have h := hN (m, l) ⟨le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hl⟩
  simp only [Set.mem_preimage, Function.comp, Prod.map, Seminorm.mem_ball, sub_zero] at h
  rwa [map_sub_rev] at h
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
[all_cauchy_implies_cauchySeq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
lemma all_cauchy_implies_cauchySeq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {u : ℕ → 𝓢(E, F)}
-- given
  (hcauchy : ∀ (k n : ℕ), ∀ ε > 0, ∃ N, ∀ a b, N ≤ a → N ≤ b → SchwartzMap.seminorm ℝ k n (u a - u b) < ε) :
-- imply
  CauchySeq u := by
-- proof
  have hws := schwartz_withSeminorms ℝ E F
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  erw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf _).mp hws]
  rw [Filter.tendsto_iInf]
  intro ⟨k, n⟩
  rw [Filter.tendsto_comap_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy k n ε hε
  refine ⟨(N, N), fun ⟨a, b⟩ ⟨ha, hb⟩ => ?_⟩
  simp only [Function.comp_def, Prod.map_apply, dist_zero_right, Real.norm_eq_abs,
    SchwartzMap.schwartzSeminormFamily_apply]
  rw [abs_of_nonneg (by positivity : 0 ≤ (SchwartzMap.seminorm ℝ k n) (u b - u a)),
    map_sub_rev]
  exact hN a b ha hb
noncomputable section

/--
[diag_cauchy_implies_cauchySeq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
lemma diag_cauchy_implies_cauchySeq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {u : ℕ → 𝓢(E, F)}
-- given
  (hcauchy : ∀ K : ℕ, ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - u m) < ε) :
-- imply
  CauchySeq u := by
-- proof
  apply all_cauchy_implies_cauchySeq u
  intro k n ε hε
  set K := max k n
  obtain ⟨N, hN⟩ := hcauchy K ε hε
  refine ⟨N, fun a b ha hb => ?_⟩
  calc SchwartzMap.seminorm ℝ k n (u a - u b)
    ≤ (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u a - u b) :=
      SchwartzSeminorms.individual_le_sup_seminorm (le_max_left k n) (le_max_right k n) _
    _ < ε := hN a b ha hb
namespace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/--
[iterFDeriv_sub_le_seminorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
private lemma iterFDeriv_sub_le_seminorm_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  {u : ℕ → 𝓢(E, F)}
  {n m l : ℕ}
  {x : E} :
-- imply
  ‖iteratedFDeriv ℝ n (↑(u m)) x - iteratedFDeriv ℝ n (↑(u l)) x‖ ≤ SchwartzMap.seminorm ℝ 0 n (u m - u l) := by
-- proof
  apply iterFDeriv_sub_le_seminorm u n m l x

/--
[schwartz_cauchySeq_limit_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
private lemma schwartz_cauchySeq_limit_contDiff_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
-- given
  (hu : CauchySeq u) :
-- imply
  ∃ g : E → F, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ n x, Tendsto (fun m => iteratedFDeriv ℝ n (↑(u m)) x) atTop (nhds (iteratedFDeriv ℝ n g x))) := by
-- proof
  apply schwartz_cauchySeq_limit_contDiff u hu

/--
[instCompleteSpaceSchwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzComplete.lean)
-/
@[path]
private lemma instCompleteSpaceSchwartz_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F] :
-- imply
  CompleteSpace 𝓢(E, F) := by
-- proof
  apply instCompleteSpaceSchwartz


-- created on 2026-10-23
