import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.OrthogonalityTubes
open OrthogonalityTubes
open MeasureTheory


namespace OrthogonalityTubes

/--
[l2Inner_eq_zero_of_pointwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean)
-/
@[path]
lemma l2Inner_eq_zero_of_pointwise_disjoint
  {f g : EuclideanSpace ℝ (Fin 2) → ℂ}
-- given
  (h : ∀ ξ, f ξ = 0 ∨ g ξ = 0) :
-- imply
  l2Inner f g = 0 := by
-- proof
  unfold l2Inner
  have heq : (fun x => f x * starRingEnd ℂ (g x)) = 0 := by
    ext x
    cases h x with
    | inl hf => simp [hf]
    | inr hg => simp [hg]
  rw [heq]
  simp

end OrthogonalityTubes

namespace OrthogonalityTubes

/--
[Tube.carrier_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean)
-/
@[path]
lemma Tube.carrier_nonempty
  {R : ℝ}
  {T : Tube R}
-- given
  (hR : 1 ≤ R) :
-- imply
  (T.carrier : Set (EuclideanSpace ℝ (Fin 2))).Nonempty := by
-- proof
  refine ⟨T.center, ?_⟩
  simp only [Tube.carrier, rectangleCarrier, Set.mem_setOf_eq, sub_self, inner_zero_left,
    abs_zero]
  exact ⟨by linarith, by linarith⟩

end OrthogonalityTubes

namespace OrthogonalityTubes

/--
[disjoint_thickening_infDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OrthogonalityTubes.lean)
-/
@[path]
lemma disjoint_thickening_infDist
  {R : ℝ}
  {r : ℝ}
  {T₁ T₂ : Tube R}
  {x : EuclideanSpace ℝ (Fin 2)}
-- given
  (hR : 1 ≤ R)
  (hdisjoint : Disjoint (T₁.rNeighborhood r) (T₂.rNeighborhood r)) :
-- imply
  r ≤ Metric.infDist x T₁.carrier ∨ r ≤ Metric.infDist x T₂.carrier := by
-- proof
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hx1 : x ∈ T₁.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₁)]
  have hx2 : x ∈ T₂.rNeighborhood r := by
    simp only [Tube.rNeighborhood]
    rwa [Metric.mem_thickening_iff_infDist_lt (Tube.carrier_nonempty hR T₂)]
  exact hdisjoint.ne_of_mem hx1 hx2 rfl
/-- Schwartz-type pointwise decay bound for the tube wave packet:
$|\phi_{T, r}(x)| \le r^{-1} (1 + d(x, T) / r)^{-N}$ for every $N > 0$. -/

end OrthogonalityTubes


-- created on 2026-10-23
