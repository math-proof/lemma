import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bcffaceclose
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.Walls


/--
[bcf_forest_no_contour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_forest_no_contour_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hac : G.IsAcyclic) :
-- imply
  ¬ c.IsCycle := by
-- proof
  apply StatMech.Walls.bcf_forest_no_contour hac c

/--
[bcf_acyclic_cycle_absurd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_acyclic_cycle_absurd_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hac : G.IsAcyclic)
  (hc : c.IsCycle) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bcf_acyclic_cycle_absurd hac hc

/--
[bcf_cycle_three_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_cycle_three_le_length_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  3 ≤ c.length := by
-- proof
  apply StatMech.Walls.bcf_cycle_three_le_length hc

/--
[bcf_no_forest_contour_for_faceCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_no_forest_contour_for_faceCut_eq
  {d : ℕ}
  {a : Site 2}
  {G : SimpleGraph (Site 2)}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hGle : G ≤ hypercubicLattice 2)
  (hGac : G.IsAcyclic)
  (hcyc : Vc.IsCycle)
  (hedges : ∀ e ∈ Vc.edges, e ∈ G.edgeSet) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bcf_no_forest_contour_for_faceCut hGle hGac Vc hcyc hedges

/--
[bcf_vertexBoundary_is_site_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_vertexBoundary_is_site_shell_eq
  {d : ℕ}
  {d R : ℕ} :
-- imply
  vertexBoundary d R = box d R \ box d (R - 1) := by
-- proof
  apply StatMech.Walls.bcf_vertexBoundary_is_site_shell d R

/--
[bcf_faceCut_is_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_faceCut_is_edgeSet_eq
  {d : ℕ}
-- given
  (T : Site 2 → Prop) :
-- imply
  jed_cutSet T = {e : Sym2 (Site 2) | ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧ e = sharedPrimalEdge a b ∧ (T a ↔ ¬ T b)} := by
-- proof
  apply StatMech.Walls.bcf_faceCut_is_edgeSet T

/--
[bcf_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcffaceclose.lean)
-/
@[path]
private lemma bcf_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} {G : SimpleGraph V}, G.IsAcyclic → ∀ {v : V} (c : G.Walk v v), ¬ c.IsCycle) ∧ (∀ {V : Type} {G : SimpleGraph V} {v : V} {c : G.Walk v v}, c.IsCycle → 3 ≤ c.length) ∧ (∀ {a : Site 2} {G : SimpleGraph (Site 2)}, G ≤ hypercubicLattice 2 → G.IsAcyclic → ∀ (Vc : (hypercubicLattice 2).Walk a a), Vc.IsCycle → (∀ e ∈ Vc.edges, e ∈ G.edgeSet) → False) ∧ (∀ (d R : ℕ), vertexBoundary d R = box d R \ box d (R - 1)) := by
-- proof
  apply StatMech.Walls.bcf_status


-- created on 2026-10-23
