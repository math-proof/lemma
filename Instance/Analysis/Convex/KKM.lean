-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.

module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic
public import Def.Analysis.Convex.KKM
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

@[expose] public section

namespace Convex.KKM

variable {n : ℕ}

instance bdVDecEq : ∀ k, DecidableEq (BdV (n := n) k)
  | 0 => by change DecidableEq (Fin (n + 1)); exact inferInstance
  | k + 1 => by
      change DecidableEq (Finset (BdV (n := n) k))
      have : DecidableEq (BdV (n := n) k) := bdVDecEq k
      exact inferInstance

instance bdVFin : ∀ k, Fintype (BdV (n := n) k)
  | 0 => by change Fintype (Fin (n + 1)); exact inferInstance
  | k + 1 => by
      change Fintype (Finset (BdV (n := n) k))
      have : Fintype (BdV (n := n) k) := bdVFin k
      have : DecidableEq (BdV (n := n) k) := bdVDecEq k
      exact inferInstance

end Convex.KKM
