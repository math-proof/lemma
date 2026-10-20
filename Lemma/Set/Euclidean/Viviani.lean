import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Viviani
open MetaMathlibExt


/--
[viviani_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Viviani.lean)
-/
@[path]
private lemma viviani_general_eq
  :
-- imply
  ∀ (A B C P : EuclideanSpace ℝ (Fin 2)),
    dist A B = dist B C → dist B C = dist C A →
    P ∈ interior (convexHull ℝ {A, B, C}) →
    Metric.infDist P ↑(affineSpan ℝ {A, B}) +
    Metric.infDist P ↑(affineSpan ℝ {B, C}) +
    Metric.infDist P ↑(affineSpan ℝ {C, A}) =
    Metric.infDist A ↑(affineSpan ℝ {B, C}) := by
-- proof
  apply MetaMathlibExt.viviani_general

/--
[viviani](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Viviani.lean)
-/
@[path]
private lemma viviani_eq
  :
-- imply
  ∀ (A B C P : EuclideanSpace ℝ (Fin 2)),
    dist A B = dist B C → dist B C = dist C A → 0 < dist A B →
    P ∈ interior (convexHull ℝ {A, B, C}) →
    Metric.infDist P ↑(affineSpan ℝ {A, B}) +
    Metric.infDist P ↑(affineSpan ℝ {B, C}) +
    Metric.infDist P ↑(affineSpan ℝ {C, A}) =
    Metric.infDist A ↑(affineSpan ℝ {B, C}) := by
-- proof
  apply MetaMathlibExt.viviani


-- created on 2026-10-20
