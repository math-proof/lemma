import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.InterceptTheorem
open MetaMathlibExt


/--
[intercept_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/InterceptTheorem.lean)
-/
@[path]
private lemma intercept_theorem_eq
  :
-- imply
  ∀ (A B C D E : EuclideanSpace ℝ (Fin 2)),
    dist A D + dist D B = dist A B →
    0 < dist A D →
    0 < dist D B →
    dist A E + dist E C = dist A C →
    0 < dist A E →
    0 < dist E C →
    (¬ ∃ t : ℝ, C - A = t • (B - A)) →
    (∃ r : ℝ, r ≠ 0 ∧ E - D = r • (C - B)) →
    dist A D / dist D B = dist A E / dist E C := by
-- proof
  apply MetaMathlibExt.intercept_theorem


-- created on 2026-10-20
