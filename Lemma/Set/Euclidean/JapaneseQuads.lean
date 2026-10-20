import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.JapaneseQuads
open MetaMathlibExt


/--
[japanese_theorem_concyclic_quadrilaterals](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/JapaneseQuads.lean)
-/
@[path]
private lemma japanese_theorem_concyclic_quadrilaterals_eq
  :
-- imply
  ∀ (A B C D : EuclideanSpace ℝ (Fin 2)) (r1 r2 r3 r4 : ℝ),
    (∃ O : EuclideanSpace ℝ (Fin 2), ∃ R : ℝ, 0 < R ∧
    A ∈ Metric.sphere O R ∧ B ∈ Metric.sphere O R ∧
    C ∈ Metric.sphere O R ∧ D ∈ Metric.sphere O R) →
    (segment ℝ A C ∩ segment ℝ B D).Nonempty →
    A ≠ B → B ≠ C → C ≠ D → D ≠ A → A ≠ C → B ≠ D →
    0 < r1 → 0 < r2 → 0 < r3 → 0 < r4 →
    (∃ I1 : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall I1 r1 ⊆ convexHull ℝ {A, B, C} ∧
    (segment ℝ A B ∩ Metric.sphere I1 r1).Nonempty ∧
    (segment ℝ B C ∩ Metric.sphere I1 r1).Nonempty ∧
    (segment ℝ C A ∩ Metric.sphere I1 r1).Nonempty) →
    (∃ I2 : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall I2 r2 ⊆ convexHull ℝ {C, D, A} ∧
    (segment ℝ C D ∩ Metric.sphere I2 r2).Nonempty ∧
    (segment ℝ D A ∩ Metric.sphere I2 r2).Nonempty ∧
    (segment ℝ A C ∩ Metric.sphere I2 r2).Nonempty) →
    (∃ I3 : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall I3 r3 ⊆ convexHull ℝ {B, C, D} ∧
    (segment ℝ B C ∩ Metric.sphere I3 r3).Nonempty ∧
    (segment ℝ C D ∩ Metric.sphere I3 r3).Nonempty ∧
    (segment ℝ D B ∩ Metric.sphere I3 r3).Nonempty) →
    (∃ I4 : EuclideanSpace ℝ (Fin 2),
    Metric.closedBall I4 r4 ⊆ convexHull ℝ {D, A, B} ∧
    (segment ℝ D A ∩ Metric.sphere I4 r4).Nonempty ∧
    (segment ℝ A B ∩ Metric.sphere I4 r4).Nonempty ∧
    (segment ℝ B D ∩ Metric.sphere I4 r4).Nonempty) →
    r1 + r2 = r3 + r4 := by
-- proof
  apply MetaMathlibExt.japanese_theorem_concyclic_quadrilaterals


-- created on 2026-10-20
