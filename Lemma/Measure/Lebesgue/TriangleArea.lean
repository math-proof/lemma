import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.Lebesgue.TriangleArea
open MeasureTheory Set
open MetaMathlibExt


/--
[_root_.MeasureTheory.toReal_volume_convexHull_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma MeasureTheory_toReal_volume_convexHull_triangle_eq
  {a b c : EuclideanSpace ℝ (Fin 2)} :
-- imply
  (volume (convexHull ℝ
    ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
    |(b - a).ofLp 0 * (c - a).ofLp 1 - (b - a).ofLp 1 * (c - a).ofLp 0| / 2 := by
-- proof
  apply MeasureTheory.toReal_volume_convexHull_triangle a b c

/--
[_root_.MeasureTheory.volume_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma MeasureTheory_volume_unitSquare_eq
  :
-- imply
  volume {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} = 1 := by
-- proof
  apply MeasureTheory.volume_unitSquare


-- created on 2026-10-20
