-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Instance.Analysis.Convex.KKM
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

/-- Validity of a simplex over coordinate set `S`: level 0 means a nonempty
sub-vertex-set of `S`; higher levels mean a nonempty chain of valid
simplices. -/
def BdValid (S : Finset (Fin (n + 1))) : ∀ k, Finset (BdV (n := n) k) → Prop
  | 0, σ => σ ⊆ S ∧ σ.Nonempty
  | k + 1, σ =>
      (∀ a ∈ (σ : Set (BdV (n := n) (k + 1))), ∀ b ∈ (σ : Set (BdV (n := n) (k + 1))),
        BdFin a ⊆ BdFin b ∨ BdFin b ⊆ BdFin a) ∧
      (∀ v ∈ σ, BdValid S k v) ∧ σ.Nonempty

/-- Geometric realization: vertices go to simplex vertices; higher vertices
to barycenters. -/
noncomputable def BdPt : ∀ k, BdV (n := n) k → (Fin (n + 1) → ℝ)
  | 0, i => fun j => if j = BdFin0 i then 1 else 0
  | k + 1, σ => fun j => (∑ v ∈ BdFin σ, BdPt k v j) / ((BdFin σ).card : ℝ)

/-- Coordinate support of a vertex. -/
def BdSupp : ∀ k, BdV (n := n) k → Finset (Fin (n + 1))
  | 0, i => {BdFin0 i}
  | k + 1, σ => (BdFin σ).biUnion (BdSupp k)

end Convex.KKM
