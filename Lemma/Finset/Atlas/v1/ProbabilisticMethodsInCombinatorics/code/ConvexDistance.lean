import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.ConvexDistance
open Finset ConvexDistance
open scoped BigOperators


namespace ConvexDistance

/--
[weightedHammingDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma weightedHammingDist_nonneg
  {n : ℕ}
  {α x y : EuclideanSpace ℝ (Fin n)} :
-- imply
  0 ≤ weightedHammingDist α x y := by
-- proof
  simp only [weightedHammingDist]
  apply Finset.sum_nonneg; intro i _; split_ifs with h
  · exact abs_nonneg _
  · exact le_refl _

end ConvexDistance

namespace ConvexDistance

/--
[abs_component_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma abs_component_le_norm
  {n : ℕ}
  {α : EuclideanSpace ℝ (Fin n)}
  {i : Fin n} :
-- imply
  |α i| ≤ ‖α‖ := by
-- proof
  have h1 : (α i) ^ 2 ≤ ∑ j : Fin n, (α j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (α j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ‖α‖ ^ 2 = ∑ j : Fin n, (α j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    congr 1; funext j; rw [Real.norm_eq_abs, sq_abs]
  exact abs_le_of_sq_le_sq (h2 ▸ h1) (norm_nonneg _)

end ConvexDistance

namespace ConvexDistance

/--
[weightedHammingDist_le_of_unit_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma weightedHammingDist_le_of_unit_norm
  {n : ℕ}
  {α x y : EuclideanSpace ℝ (Fin n)}
-- given
  (hα : ‖α‖ = 1) :
-- imply
  weightedHammingDist α x y ≤ ↑n := by
-- proof
  simp only [weightedHammingDist]
  calc ∑ i : Fin n, (if x i ≠ y i then |α i| else (0 : ℝ))
    ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum; intro i _
      split_ifs with h
      · exact (abs_component_le_norm α i).trans (le_of_eq hα)
      · linarith
    _ = ↑n := by simp [Finset.sum_const]

end ConvexDistance

namespace ConvexDistance

/--
[inner_le_weightedHammingDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma inner_le_weightedHammingDist
  {n : ℕ}
  {x y : EuclideanSpace ℝ (Fin n)}
  {α : EuclideanSpace ℝ (Fin n)}
-- given
  (hx : x ∈ unitCube n)
  (hy : y ∈ unitCube n) :
-- imply
  @inner ℝ _ _ (x - y) α ≤ weightedHammingDist α x y := by
-- proof
  simp only [weightedHammingDist]
  rw [show @inner ℝ _ _ (x - y) α = ∑ i : Fin n, (x i - y i) * α i from by
    rw [PiLp.inner_apply]; congr 1; ext i; simp [PiLp.sub_apply, inner, mul_comm]]
  apply Finset.sum_le_sum; intro i _
  by_cases h : x i = y i
  · simp [h]
  · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true]
    calc (x i - y i) * α i
      ≤ |(x i - y i) * α i| := le_abs_self _
      _ = |x i - y i| * |α i| := abs_mul _ _
      _ ≤ 1 * |α i| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [abs_le]; constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
      _ = |α i| := one_mul _

end ConvexDistance

namespace ConvexDistance

/--
[talagrandDist_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma talagrandDist_bddAbove
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {A : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hAne : A.Nonempty) :
-- imply
  BddAbove ((fun α => weightedHammingDistSet α x A) '' {α | ‖α‖ = 1}) := by
-- proof
  refine ⟨↑n, ?_⟩
  rintro r ⟨α, (hα : ‖α‖ = 1), rfl⟩
  unfold weightedHammingDistSet
  obtain ⟨y₀, hy₀⟩ := hAne
  have hbdd : BddBelow ((weightedHammingDist α x) '' A) :=
    ⟨0, fun b ⟨y, _, hb⟩ => hb ▸ weightedHammingDist_nonneg α x y⟩
  exact (csInf_le hbdd (Set.mem_image_of_mem _ hy₀)).trans
    (weightedHammingDist_le_of_unit_norm α x y₀ hα)

end ConvexDistance

namespace ConvexDistance

/--
[talagrandDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma talagrandDist_nonneg
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {A : Set (EuclideanSpace ℝ (Fin n))} :
-- imply
  0 ≤ talagrandDist x A := by
-- proof
  unfold talagrandDist
  apply Real.sSup_nonneg
  rintro r ⟨α, _, rfl⟩
  unfold weightedHammingDistSet
  apply Real.sInf_nonneg
  rintro b ⟨y, _, rfl⟩
  exact weightedHammingDist_nonneg α x y

end ConvexDistance

namespace ConvexDistance

/--
[convex_dist_upper_bounds_euclidean_dist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean)
-/
@[path]
lemma convex_dist_upper_bounds_euclidean_dist
  {n : ℕ}
  {A : Set (EuclideanSpace ℝ (Fin n))}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hA : A ⊆ unitCube n)
  (hx : x ∈ unitCube n)
  (hAne : A.Nonempty) :
-- imply
  Metric.infDist x (convexHull ℝ A) ≤ talagrandDist x A := by
-- proof
  set K := closure (convexHull ℝ A)
  have hKne : K.Nonempty := hAne.mono fun a ha => subset_closure (subset_convexHull ℝ A ha)
  have hKconvex : Convex ℝ K := (convex_convexHull ℝ A).closure
  rw [← Metric.infDist_closure]
  obtain ⟨v, hv, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hKne isClosed_closure.isComplete hKconvex x
  have hdist_eq : Metric.infDist x K = ‖x - v‖ := by
    rw [Metric.infDist_eq_iInf]; simp only [dist_eq_norm]; exact hvmin.symm
  rw [hdist_eq]
  by_cases hxv : x = v
  · subst hxv; rw [sub_self, norm_zero]; exact talagrandDist_nonneg x A
  ·
    set α := (‖x - v‖⁻¹ : ℝ) • (x - v)
    have hnorm_pos : 0 < ‖x - v‖ := by
      rw [norm_pos_iff]; intro h; exact hxv (eq_of_sub_eq_zero h)
    have hα_norm : ‖α‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hnorm_pos)]
    have hA_sub_K : A ⊆ K := fun a ha => subset_closure (subset_convexHull ℝ A ha)
    have hinner_ge : ∀ y ∈ A, ‖x - v‖ ≤ @inner ℝ _ _ (x - y) α := by
      intro y hy
      show ‖x - v‖ ≤ @inner ℝ _ _ (x - y) (‖x - v‖⁻¹ • (x - v))
      rw [inner_smul_right]
      rw [real_inner_comm]
      rw [le_inv_mul_iff₀ hnorm_pos, ← sq]
      have hproj := ((norm_eq_iInf_iff_real_inner_le_zero hKconvex hv).mp hvmin) y (hA_sub_K hy)
      have key : x - y = (x - v) - (y - v) := by abel
      rw [key, inner_sub_right, real_inner_self_eq_norm_mul_norm, sq]; linarith
    have hbound : ∀ y ∈ A, ‖x - v‖ ≤ weightedHammingDist α x y := fun y hy =>
      (hinner_ge y hy).trans (inner_le_weightedHammingDist x y hx (hA hy) α)
    have hle_whdSet : ‖x - v‖ ≤ weightedHammingDistSet α x A := by
      unfold weightedHammingDistSet
      exact le_csInf (hAne.image _) (fun b ⟨y, hy, hb⟩ => hb ▸ hbound y hy)
    exact le_csSup_of_le (talagrandDist_bddAbove x A hAne) ⟨α, hα_norm, rfl⟩ hle_whdSet

end ConvexDistance


-- created on 2026-10-23
