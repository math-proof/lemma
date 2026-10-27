import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
open Finset BigOperators Set Metric AlgebraicTopologyI SubdivisionDiameter LocalityPrinciple
open CategoryTheory AlgebraicTopology BarycentricSubdivision


namespace AlgebraicTopologyI

/--
[lebesgue_covering_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma lebesgue_covering_lemma
  [PseudoMetricSpace M]
  [CompactSpace M]
  {U : ι → Set M}
-- given
  (hU_open : ∀ i, IsOpen (U i))
  (hU_cover : (Set.univ : Set M) ⊆ ⋃ i, U i) :
-- imply
  ∃ ε > 0, ∀ x : M, ∃ i, ball x ε ⊆ U i := by
-- proof
  obtain ⟨δ, hδ_pos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU_open hU_cover
  exact ⟨δ, hδ_pos, fun x => hδ x (mem_univ x)⟩
end AlgebraicTopologyI
noncomputable section


namespace SubdivisionDiameter

/--
[barycenter_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma barycenter_sub_vertex
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 1) → E}
  {i : Fin (n + 1)} :
-- imply
  barycenter n v - v i = (↑(n + 1) : ℝ)⁻¹ • ∑ j : Fin (n + 1), (v j - v i) := by
-- proof
  unfold barycenter; rw [Finset.sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_sub]; congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀]
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[barycenter_mem_convexHull](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma barycenter_mem_convexHull
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 1) → E} :
-- imply
  barycenter n v ∈ convexHull ℝ (range v) := by
-- proof
  unfold barycenter
  rw [show (↑(n + 1) : ℝ)⁻¹ • ∑ i, v i =
    Finset.univ.centerMass (fun _ : Fin (n + 1) => (1 : ℝ)) v from ?_]
  · exact centerMass_mem_convexHull _ (fun _ _ => le_of_lt one_pos)
    (by simp; positivity) (fun i _ => mem_range.mpr ⟨i, rfl⟩)
  · unfold Finset.centerMass
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_smul]

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[dist_barycenter_vertex_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma dist_barycenter_vertex_le
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 1) → E}
  {i : Fin (n + 1)} :
-- imply
  dist (barycenter n v) (v i) ≤ (n : ℝ) / (n + 1) * diam (range v) := by
-- proof
  rw [dist_eq_norm, barycenter_sub_vertex]
  have hn1 : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hbdd : Bornology.IsBounded (range v) := (finite_range v).isBounded
  have hsum : ∑ j : Fin (n + 1), (v j - v i) = ∑ j ∈ univ.erase i, (v j - v i) := by
    rw [← add_sum_erase _ _ (mem_univ i)]; simp
  rw [hsum]
  calc ‖(↑(n + 1) : ℝ)⁻¹ • ∑ j ∈ univ.erase i, (v j - v i)‖
    = (↑(n + 1) : ℝ)⁻¹ * ‖∑ j ∈ univ.erase i, (v j - v i)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn1)]
    _ ≤ (↑(n + 1) : ℝ)⁻¹ * ∑ j ∈ univ.erase i, ‖v j - v i‖ := by
      gcongr; exact norm_sum_le _ _
    _ ≤ (↑(n + 1) : ℝ)⁻¹ * ∑ j ∈ univ.erase i, diam (range v) := by
      gcongr with j _
      rw [← dist_eq_norm]; exact dist_le_diam_of_mem hbdd ⟨j, rfl⟩ ⟨i, rfl⟩
    _ = (↑(n + 1) : ℝ)⁻¹ * (↑n * diam (range v)) := by
      congr 1; rw [sum_const, card_erase_of_mem (mem_univ i), card_univ,
        Fintype.card_fin, Nat.succ_sub_one, nsmul_eq_mul]
    _ = _ := by push_cast; ring

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[dist_barycenter_convexHull_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma dist_barycenter_convexHull_le
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 1) → E}
  {p : E}
-- given
  (hp : p ∈ convexHull ℝ (range v)) :
-- imply
  dist (barycenter n v) p ≤ (n : ℝ) / (n + 1) * diam (range v) := by
-- proof
  obtain ⟨x, hx, hpx⟩ := convexHull_exists_dist_ge hp (barycenter n v)
  obtain ⟨j, rfl⟩ := mem_range.mp hx
  calc dist (barycenter n v) p = dist p (barycenter n v) := dist_comm _ _
    _ ≤ dist (v j) (barycenter n v) := hpx
    _ = dist (barycenter n v) (v j) := dist_comm _ _
    _ ≤ _ := dist_barycenter_vertex_le n v j

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[range_comp_succAbove_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma range_comp_succAbove_subset
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 2) → E}
  {k : Fin (n + 2)} :
-- imply
  range (v ∘ Fin.succAbove k) ⊆ range v :=
-- proof
  fun _ ⟨i, hi⟩ => ⟨Fin.succAbove k i, hi⟩

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[subdivSimplex_subset_convexHull](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma subdivSimplex_subset_convexHull
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E] :
-- imply
  ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E}, IsSubdivSimplex v τ → τ ⊆ convexHull ℝ (range v) := by
-- proof
  intro n v τ hτ; induction hτ with
  | point v => intro x hx; simp only [mem_singleton_iff] at hx; rw [hx]; exact subset_convexHull ℝ _ ⟨0, rfl⟩
  | cone v k τ _ ih =>
    intro x hx; simp only [mem_insert_iff] at hx
    obtain rfl | hx := hx
    · exact barycenter_mem_convexHull _ v
    · exact convexHull_mono (range_comp_succAbove_subset v k) (ih hx)

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[subdivSimplex_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma subdivSimplex_isBounded
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E] :
-- imply
  ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E}, IsSubdivSimplex v τ → Bornology.IsBounded τ := by
-- proof
  intro n v τ hτ; induction hτ with
  | point _ => exact (finite_singleton _).isBounded
  | cone _ _ _ _ ih => exact ih.insert _

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[diam_face_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma diam_face_le
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {v : Fin (n + 2) → E}
  {k : Fin (n + 2)} :
-- imply
  diam (range (v ∘ Fin.succAbove k)) ≤ diam (range v) :=
-- proof
  Metric.diam_mono (range_comp_succAbove_subset v k) (finite_range v).isBounded

end SubdivisionDiameter

namespace SubdivisionDiameter

/--
[diam_subdivSimplex_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma diam_subdivSimplex_le
  [SeminormedAddCommGroup E]
  [NormedSpace ℝ E] :
-- imply
  ∀ {n : ℕ} {v : Fin (n + 1) → E} {τ : Set E}, IsSubdivSimplex v τ → diam τ ≤ (n : ℝ) / (n + 1) * diam (range v) := by
-- proof
  intro n v τ hτ
  induction hτ with
  | point v => simp [diam_singleton]
  | @cone n v k τ hτ_face ih =>
    have hτ_cvx : τ ⊆ convexHull ℝ (range v) := fun x hx =>
      subdivSimplex_subset_convexHull
        (IsSubdivSimplex.cone v k τ hτ_face) (mem_insert_of_mem _ hx)
    have hτ_bdd := subdivSimplex_isBounded hτ_face
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    intro x hx y hy
    simp only [mem_insert_iff] at hx hy
    have h_mono : (↑n : ℝ) / (↑n + 1) ≤ (↑n + 1) / (↑n + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h_diam_nn : (0 : ℝ) ≤ diam (range v) := diam_nonneg
    obtain rfl | hx <;> rcases hy with rfl | hy := hx
    · simp only [dist_self]; positivity
    · exact dist_barycenter_convexHull_le (n + 1) v y (hτ_cvx hy)
    · rw [dist_comm]
      exact dist_barycenter_convexHull_le (n + 1) v x (hτ_cvx hx)
    · calc dist x y ≤ diam τ := dist_le_diam_of_mem hτ_bdd hx hy
      _ ≤ ↑n / (↑n + 1) * diam (range (v ∘ Fin.succAbove k)) := ih
      _ ≤ ↑n / (↑n + 1) * diam (range v) := by
        gcongr; exact diam_face_le v k
      _ ≤ (↑n + 1) / (↑n + 2) * diam (range v) :=
        mul_le_mul_of_nonneg_right h_mono h_diam_nn
      _ = ↑(n + 1) / (↑(n + 1) + 1) * diam (range v) := by push_cast; ring
end SubdivisionDiameter
namespace LocalityPrinciple
open CategoryTheory AlgebraicTopology BarycentricSubdivision


namespace LocalityPrinciple

/--
[endoPow_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma endoPow_succ
  {C : ChainComplex AddCommGrpCat ℕ}
  {f : C ⟶ C}
  {n : ℕ} :
-- imply
  endoPow f (n + 1) = f ≫ endoPow f n :=
-- proof
  rfl

end LocalityPrinciple

namespace LocalityPrinciple

/--
[iterated_subdivision_homotopic_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
lemma iterated_subdivision_homotopic_id
  {X : TopCat.{0}}
  {k : ℕ} :
-- imply
  Nonempty (Homotopy (endoPow (subdivisionOperator.app X) k) (𝟙 (singularChainFunctorZ.obj X))) :=
-- proof
  ⟨iteratedSubdivisionHomotopy X k⟩
end LocalityPrinciple
end


/--
[endoPow_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean)
-/
@[path]
private lemma endoPow_zero_eq
  {C : ChainComplex AddCommGrpCat ℕ}
  {f : C ⟶ C} :
-- imply
  endoPow f 0 = 𝟙 C := by
-- proof
  apply LocalityPrinciple.endoPow_zero f


-- created on 2026-10-23
