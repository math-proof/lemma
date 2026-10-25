-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Knaster-Kuratowski-Mazurkiewicz lemma

Proved via Sperner's lemma on iterated barycentric subdivisions plus a
mesh-shrinking limit argument: fully labeled simplices at every level, a
convergent subsequence in the compact simplex (mesh `(n/(n+1))^k → 0`), and
closedness of the cover. Vertices at level `k+1` are finsets of level-`k`
vertices; validity means a nonempty chain with supports in the coordinate
set; `BdPt` is barycentric realization in `Convexity.StdSimplex`.

Primary source: B. Knaster, C. Kuratowski, S. Mazurkiewicz,
"Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe",
Fundamenta Mathematicae 14 (1929), 132–137, DOI 10.4064/fm-14-1-132-137.
-/


namespace Convex.KKM

variable {n : ℕ}

/-- Vertices at subdivision level `k`: level 0 is `Fin (n+1)`; higher levels
are (valid) simplices of the previous level, as bare finsets. -/
def BdV : ℕ → Type
  | 0 => Fin (n + 1)
  | k + 1 => Finset (BdV k)

/-- View a higher-level vertex as a finset (explicit projection so that
unification sees the `Finset` type; bare ascriptions do not propagate). -/
def BdFin {k : ℕ} (a : BdV (n := n) (k + 1)) : Finset (BdV (n := n) k) := a

/-- View a level-0 vertex as a simplex index. -/
def BdFin0 (i : BdV (n := n) 0) : Fin (n + 1) := i

end Convex.KKM
