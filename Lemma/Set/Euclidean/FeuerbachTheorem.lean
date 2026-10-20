import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.FeuerbachTheorem
open Affine Affine.Simplex EuclideanGeometry
open scoped InnerProductSpace
open MetaMathlibExt


/--
[Feuerbach_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/FeuerbachTheorem.lean)
-/
@[path]
private lemma Feuerbach_theorem_eq
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] [Fact (Module.finrank ℝ V = 2)]
  {s : Affine.Triangle ℝ P} :
-- imply
  (¬ (dist (s.points 0) (s.points 1) = dist (s.points 1) (s.points 2) ∧
    dist (s.points 1) (s.points 2) = dist (s.points 2) (s.points 0)) →
    (∃ F, s.insphere.IsIntTangentAt s.ninePointCircle F ∧
    ∀ G, G ∈ s.insphere → G ∈ s.ninePointCircle → G = F)) ∧
    ∀ i, s.ninePointCircle.IsExtTangent (s.exsphere {i}) := by
-- proof
  apply MetaMathlibExt.Feuerbach_theorem s


-- created on 2026-10-20
