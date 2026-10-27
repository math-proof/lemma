import Mathlib
import Initialize.Tactic.Attr.Basic
open Set Finset


/--
[lemma_1_15_linear_max_at_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_15.lean)
-/
@[path]
lemma lemma_1_15_linear_max_at_vertex
  [AddCommGroup E]
  [Module ℝ E]
  {f : E →ₗ[ℝ] ℝ}
  {S : Finset E}
  {x : E}
-- given
  (hS : S.Nonempty)
  (hx : x ∈ convexHull ℝ (↑S : Set E)) :
-- imply
  f x ≤ S.sup' hS f :=
-- proof
  (f.convexOn (convex_convexHull ℝ (↑S : Set E))).le_sup_of_mem_convexHull
    (subset_convexHull ℝ (↑S : Set E)) hx

/--
[lemma_1_15_exists_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_15.lean)
-/
@[path]
lemma lemma_1_15_exists_vertex
  [AddCommGroup E]
  [Module ℝ E]
  {f : E →ₗ[ℝ] ℝ}
  {S : Finset E}
  {x : E}
-- given
  (hx : x ∈ convexHull ℝ (↑S : Set E)) :
-- imply
  ∃ v ∈ S, f x ≤ f v := by
-- proof
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hx
  have h := (f.convexOn (convex_convexHull ℝ (↑S : Set E))).le_sup_of_mem_convexHull
    (subset_convexHull ℝ (↑S : Set E)) hx
  rwa [Finset.le_sup'_iff] at h

/--
[lemma_1_15_sSup_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Lemma_1_15.lean)
-/
@[path]
lemma lemma_1_15_sSup_eq
  [AddCommGroup E]
  [Module ℝ E]
  {f : E →ₗ[ℝ] ℝ}
  {S : Finset E}
-- given
  (hS : S.Nonempty) :
-- imply
  sSup (f '' (convexHull ℝ (↑S : Set E))) = S.sup' hS f := by
-- proof
  apply le_antisymm
  ·
    apply csSup_le
    · exact image_nonempty.mpr (convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hS))
    · rintro _ ⟨x, hx, rfl⟩
      exact lemma_1_15_linear_max_at_vertex f S hS x hx
  ·
    apply Finset.sup'_le hS
    intro v hv
    apply le_csSup
    ·
      exact ⟨S.sup' hS f, fun _ ⟨x, hx, he⟩ => he ▸ lemma_1_15_linear_max_at_vertex f S hS x hx⟩
    · exact ⟨v, subset_convexHull ℝ (↑S : Set E) (Finset.mem_coe.mpr hv), rfl⟩


-- created on 2026-10-23
