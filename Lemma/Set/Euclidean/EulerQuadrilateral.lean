import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.EulerQuadrilateral


/--
[MetaMathlibExt.euler_quadrilateral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/EulerQuadrilateral.lean)
-/
@[path]
private lemma MetaMathlibExt_euler_quadrilateral_eq
  {A B C D : EuclideanSpace ℝ (Fin 2)} :
-- imply
  dist A B ^ 2 + dist B C ^ 2 + dist C D ^ 2 + dist D A ^ 2 =
      dist A C ^ 2 + dist B D ^ 2 +
        4 * dist ((2 : ℝ)⁻¹ • (A + C)) ((2 : ℝ)⁻¹ • (B + D)) ^ 2 := by
-- proof
  apply MetaMathlibExt.euler_quadrilateral


-- created on 2026-10-20
