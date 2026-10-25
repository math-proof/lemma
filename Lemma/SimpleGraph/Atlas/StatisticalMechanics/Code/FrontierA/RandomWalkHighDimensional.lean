import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensional
open Filter Finset Topology StatMech StatMech.FrontierA


/--
[highDimensionalRandomWalk_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensional.lean)
-/
@[path]
private lemma highDimensionalRandomWalk_bound_eq
  {d : ℕ}
  {betaC epsilon sigma C c : ℝ}
  {twoPoint : ℝ → Site d → ℝ}
  {xi : ℝ → ℝ}
  {H : HighDimensionalRandomWalkHypotheses d betaC epsilon sigma C c twoPoint xi}
  {beta : ℝ}
  {x : Site d}
-- given
  (hbeta : beta ≤ betaC) :
-- imply
  twoPoint beta x ≤ latticeOriginDelta d x + highDimensionalRandomWalkTail d epsilon sigma C c (xi beta) (latticeEuclideanRadius d x) := by
-- proof
  apply StatMech.FrontierA.highDimensionalRandomWalk_bound H hbeta x


-- created on 2026-10-23
