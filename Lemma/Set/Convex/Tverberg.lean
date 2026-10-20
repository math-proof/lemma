import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.Tverberg
open MathlibExt.Geometry.Convex.TverbergWanted


/--
[tverberg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/Tverberg.lean)
-/
@[path]
private lemma tverberg_eq
  {d r : ℕ}
  {pts : Fin ((d + 1) * (r - 1) + 1) → EuclideanSpace ℝ (Fin d)}
-- given
  (hr : 0 < r) :
-- imply
  ∃ (P : Fin r → Set (Fin ((d + 1) * (r - 1) + 1)))
    (x : EuclideanSpace ℝ (Fin d)),
    (∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (P i₁) (P i₂)) ∧
    (⋃ j, P j) = Set.univ ∧
    ∀ j, x ∈ convexHull ℝ (pts '' P j) := by
-- proof
  apply MathlibExt.Geometry.Convex.TverbergWanted.tverberg hr pts


-- created on 2026-10-20
