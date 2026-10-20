import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.BeckmanQuarles
open InnerProductSpace
open MathlibExt.Geometry.Euclidean.BeckmanQuarlesWanted


/--
[beckman_quarles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/BeckmanQuarles.lean)
-/
@[path]
private lemma beckman_quarles_eq
  {n : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
-- given
  (hn : 2 ≤ n)
  (hf : ∀ x y : EuclideanSpace ℝ (Fin n), dist x y = 1 → dist (f x) (f y) = 1) :
-- imply
  Isometry f := by
-- proof
  apply MathlibExt.Geometry.Euclidean.BeckmanQuarlesWanted.beckman_quarles hn f hf


-- created on 2026-10-20
