import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.Lebesgue.TriangleArea
open MeasureTheory Set
open MetaMathlibExt


namespace MetaMathlibExt

/--
[standardTriangle_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma standardTriangle_isCompact : IsCompact standardTriangle := by
  rw [standardTriangle]
  exact (by simp : Set.Finite
    ({0, euclideanPlaneBasis 0, euclideanPlaneBasis 1} :
      Set (EuclideanSpace ℝ (Fin 2)))).isCompact_convexHull ℝ

end MetaMathlibExt

namespace MetaMathlibExt

/--
[standardTriangle_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma standardTriangle_measurableSet : MeasurableSet standardTriangle :=
  standardTriangle_isCompact.isClosed.measurableSet

end MetaMathlibExt

namespace MetaMathlibExt

/--
[measurePreserving_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma measurePreserving_reflect :
  MeasurePreserving reflect volume volume := by
  change MeasurePreserving
    ((fun x : EuclideanSpace ℝ (Fin 2) ↦ euclideanPlaneBasis 0 + euclideanPlaneBasis 1 + x) ∘
      fun x ↦ -x) volume volume
  exact (measurePreserving_add_left volume (euclideanPlaneBasis 0 + euclideanPlaneBasis 1)).comp
    (LinearIsometryEquiv.neg ℝ).measurePreserving

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unitSquare_eq_parallelepiped](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
private lemma unitSquare_eq_parallelepiped :
  {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} =
    parallelepiped euclideanPlaneBasis := by
  rw [show parallelepiped euclideanPlaneBasis =
    parallelepiped (euclideanPlaneBasis).toBasis from rfl,
    parallelepiped_basis_eq]
  ext x
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[volume_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Lebesgue/TriangleArea.lean)
-/
@[path]
lemma _root_.MeasureTheory.volume_unitSquare :
  volume {x : EuclideanSpace ℝ (Fin 2) | ∀ i, 0 ≤ x.ofLp i ∧ x.ofLp i ≤ 1} = 1 := by
  rw [unitSquare_eq_parallelepiped]
  exact (euclideanPlaneBasis).volume_parallelepiped

end MetaMathlibExt

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
-- updated on 2026-10-23
