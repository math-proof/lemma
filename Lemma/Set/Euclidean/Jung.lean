import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.Jung
open Finset BigOperators InnerProductSpace
open MathlibExt.Geometry.Euclidean.JungWanted


/--
[jung](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/Jung.lean)
-/
@[path]
private lemma jung_eq
  {n : ℕ}
  {s : Set (EuclideanSpace ℝ (Fin n))}
-- given
  (hn : 0 < n)
  (hs : Bornology.IsBounded s) :
-- imply
  ∃ c : EuclideanSpace ℝ (Fin n),
    s ⊆ Metric.closedBall c (Real.sqrt ((n : ℝ) / (2 * ((n : ℝ) + 1))) * Metric.diam s) := by
-- proof
  apply MathlibExt.Geometry.Euclidean.JungWanted.jung hn s hs


-- created on 2026-10-20
