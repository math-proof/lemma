import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[monge_three_circles_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/MongeCircles.lean)
-/
@[path]
lemma monge_three_circles_general
  [AddCommGroup V] [Module ℝ V]
  {c₁ c₂ c₃ : V}
  {r₁ r₂ r₃ : ℝ}
-- given
  (h0 : r₁ ≠ r₂)
  (h1 : r₂ ≠ r₃)
  (h2 : r₁ ≠ r₃) :
-- imply
  Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
    (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
    (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set V) := by
-- proof
  have d12 : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr h12
  have d23 : r₂ - r₃ ≠ 0 := sub_ne_zero.mpr h23
  have d13 : r₁ - r₃ ≠ 0 := sub_ne_zero.mpr h13
  obtain hr₂' | hr₂' := eq_or_ne r₂ 0
  · have e : (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁) = (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂) := by
    subst hr₂'
    match_scalars <;> field_simp <;> ring
    rw [e, Set.insert_eq_of_mem (Set.mem_insert _ _)]
    exact collinear_pair ℝ _ _
  · have hmem : (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁) ∈
    affineSpan ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨r₁ * (r₂ - r₃) / (r₂ * (r₁ - r₃)), ?_⟩
    rw [AffineMap.lineMap_apply]
    simp only [vadd_eq_add, vsub_eq_sub]
    match_scalars <;> field_simp <;> ring
    have hcol : Collinear ℝ ({(r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁),
      (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) :=
      collinear_insert_of_mem_affineSpan_pair hmem
    have hset : ({(r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁),
      (r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂)} : Set V) =
      {(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
      (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
      (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at hcol
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[monge_three_circles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/MongeCircles.lean)
-/
@[path]
lemma monge_three_circles
  {c₁ c₂ c₃ : EuclideanSpace ℝ (Fin 2)}
  {r₁ r₂ r₃ : ℝ}
-- given
  (hr₁ : 0 < r₁)
  (hr₂ : 0 < r₂)
  (hr₃ : 0 < r₃)
  (h0 : r₁ ≠ r₂)
  (h1 : r₂ ≠ r₃)
  (h2 : r₁ ≠ r₃)
  (hd12 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₂ r₂))
  (hd23 : Disjoint (Metric.closedBall c₂ r₂) (Metric.closedBall c₃ r₃))
  (hd13 : Disjoint (Metric.closedBall c₁ r₁) (Metric.closedBall c₃ r₃)) :
-- imply
  Collinear ℝ ({(r₁ - r₂)⁻¹ • (r₁ • c₂ - r₂ • c₁),
    (r₂ - r₃)⁻¹ • (r₂ • c₃ - r₃ • c₂),
    (r₁ - r₃)⁻¹ • (r₁ • c₃ - r₃ • c₁)} : Set (EuclideanSpace ℝ (Fin 2))) :=
-- proof
  monge_three_circles_general h12 h23 h13

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
