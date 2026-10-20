import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.ConwayCircle
open MetaMathlibExt


/--
[conway_circle_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/ConwayCircle.lean)
-/
@[path]
private lemma conway_circle_theorem_eq
  {A B C : EuclideanSpace ℝ (Fin 2)}
-- given
  (hABC : AffineIndependent ℝ (![A, B, C] : Fin 3 → EuclideanSpace ℝ (Fin 2))) :
-- imply
  ∃ (O : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
    A + (dist B C / dist A B) • (A - B) ∈ Metric.sphere O r ∧
    B + (dist A C / dist A B) • (B - A) ∈ Metric.sphere O r ∧
    B + (dist A C / dist B C) • (B - C) ∈ Metric.sphere O r ∧
    C + (dist A B / dist B C) • (C - B) ∈ Metric.sphere O r ∧
    C + (dist A B / dist A C) • (C - A) ∈ Metric.sphere O r ∧
    A + (dist B C / dist A C) • (A - C) ∈ Metric.sphere O r := by
-- proof
  apply MetaMathlibExt.conway_circle_theorem A B C hABC


-- created on 2026-10-20
