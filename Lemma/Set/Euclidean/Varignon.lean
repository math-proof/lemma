import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Varignon
open scoped EuclideanSpace
open MetaMathlibExt


/--
[varignon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Varignon.lean)
-/
@[path]
private lemma varignon_eq
  :
-- imply
  ∀ (A B C D P Q R S : EuclideanSpace ℝ (Fin 2)),
    2 • P = A + B → 2 • Q = B + C → 2 • R = C + D → 2 • S = D + A →
    P + R = Q + S ∧
    2 * (EuclideanGeometry.orientedTriangleArea P Q R +
    EuclideanGeometry.orientedTriangleArea P R S) =
    EuclideanGeometry.orientedTriangleArea A B C +
    EuclideanGeometry.orientedTriangleArea A C D := by
-- proof
  apply MetaMathlibExt.varignon


-- created on 2026-10-20
