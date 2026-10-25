-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Theorem.Analysis.Convex.KKM.Part2
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

/-- Sperner labeling derived from the closed cover (0 on invalid vertices). -/
noncomputable def BdLabel {k : ℕ}
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i)
    (S : Finset (Fin (n + 1))) (v : BdV (n := n) k) : Fin (n + 1) := by
  classical
  exact dite (BdValid S k {v})
    (fun hv => Classical.choose (BdLabel_exists F hF_cover v hv)) (fun _ => 0)

end Convex.KKM
