-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Convex.KKM.Part3
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

/-- Coordinate characteristic for the new-simplex packaging. -/
lemma BdSimp_weights {S : Finset (Fin (n + 1))}
    {k : ℕ} {v : BdV (n := n) k} (hv : BdValid S k {v}) (j : Fin (n + 1)) :
    (BdSimp hv).weights j = BdPt k v j := rfl

/-- Every valid vertex has a support coordinate whose closed cover set
contains the vertex point. -/
lemma BdLabel_exists {k : ℕ}
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i)
    {S : Finset (Fin (n + 1))}
    (v : BdV (n := n) k) (hv : BdValid S k {v}) :
    ∃ i, i ∈ BdSupp k v ∧ BdSimp hv ∈ F i := by
  obtain ⟨i, hi_pos, hiF⟩ := hF_cover (BdSimp hv)
  refine ⟨i, ?_, hiF⟩
  by_contra hcon
  have h0 : BdPt k v i = 0 := BdPt_eq_zero_of_not_mem_supp hcon
  have hcoe : (BdSimp hv).weights i = BdPt k v i := BdSimp_weights hv i
  rw [hcoe, h0] at hi_pos
  exact (lt_irrefl _ hi_pos).elim

end Convex.KKM
