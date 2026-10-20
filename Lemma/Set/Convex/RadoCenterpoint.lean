import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.RadoCenterpoint
open scoped InnerProductSpace
open MathlibExt.Geometry.Convex.RadoCenterpointWanted


/--
[rado_centerpoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/RadoCenterpoint.lean)
-/
@[path]
private lemma rado_centerpoint_eq
  {d n : ℕ}
  {p : Fin n → EuclideanSpace ℝ (Fin d)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ x ∈ convexHull ℝ (Set.range p),
    ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ),
    ⟪v, x⟫_ℝ ≤ t →
    n ≤ (d + 1) * Fintype.card {i : Fin n // ⟪v, p i⟫_ℝ ≤ t} := by
-- proof
  apply MathlibExt.Geometry.Convex.RadoCenterpointWanted.rado_centerpoint hn p


-- created on 2026-10-20
