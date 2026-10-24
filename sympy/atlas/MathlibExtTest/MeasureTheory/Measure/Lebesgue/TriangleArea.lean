/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Measure/Lebesgue/TriangleArea.lean -/


import sympy.atlas.MeasureTheory.Measure.Lebesgue.TriangleArea
import Lemma.Measure.Lebesgue.TriangleArea
import Mathlib.Tactic

open MeasureTheory

namespace MathlibExtTest.MeasureTheory.Measure.Lebesgue.TriangleArea

-- The coordinate right triangle has area one half.
example :
    (volume (convexHull ℝ
      ({0, (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0],
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 1]} :
        Set (EuclideanSpace ℝ (Fin 2))))).toReal = 1 / 2 := by
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  norm_num

-- A translated, non-axis-aligned triangle has area five halves.
example :
    (volume (convexHull ℝ
      ({(EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 0],
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![3, 1],
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 2]} :
        Set (EuclideanSpace ℝ (Fin 2))))).toReal = 5 / 2 := by
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  norm_num

-- A collinear triple has zero area.
example :
    (volume (convexHull ℝ
      ({(EuclideanSpace.equiv (Fin 2) ℝ).symm ![0, 0],
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![1, 1],
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![2, 2]} :
        Set (EuclideanSpace ℝ (Fin 2))))).toReal = 0 := by
  rw [MeasureTheory.toReal_volume_convexHull_triangle]
  norm_num

-- The closed unit square has real volume one.
example :
    (volume {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1}).toReal = 1 := by
  rw [MeasureTheory.volume_unitSquare]
  norm_num

end MathlibExtTest.MeasureTheory.Measure.Lebesgue.TriangleArea
