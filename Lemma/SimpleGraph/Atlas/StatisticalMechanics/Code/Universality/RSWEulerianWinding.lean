import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWEulerianWinding
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_crossEdge_eq_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWEulerianWinding.lean)
-/
@[path]
private lemma rlc_crossEdge_eq_flankFaces_eq
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  rpc_crossEdge u v = flankFaces u v := by
-- proof
  apply StatMech.Universality.rlc_crossEdge_eq_flankFaces hadj

/--
[rlc_adjacent_bdEdge_match_of_faceBoundaryTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWEulerianWinding.lean)
-/
@[path]
private lemma rlc_adjacent_bdEdge_match_of_faceBoundaryTrail_eq
  {K : Set (Site 2)}
  {f : Site 2}
  {c : (faceBoundaryGraph K).Walk f f}
  {u v : Site 2}
-- given
  (htrail : c.IsTrail)
  (hcover : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge K s(u, v) ↔ bdEdge (jec_leftRegion (c.mapLe (faceBoundaryGraph_le K))) s(u, v) := by
-- proof
  apply StatMech.Universality.rlc_adjacent_bdEdge_match_of_faceBoundaryTrail K c htrail hcover hadj

/--
[rlc_setIdentity_of_adjacent_bdEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWEulerianWinding.lean)
-/
@[path]
private lemma rlc_setIdentity_of_adjacent_bdEdge_match_eq
  {S T : Set (Site 2)}
-- given
  (hbd : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (bdEdge S s(u, v) ↔ bdEdge T s(u, v))) :
-- imply
  S = T ∨ S = Tᶜ := by
-- proof
  apply StatMech.Universality.rlc_setIdentity_of_adjacent_bdEdge_match S T hbd

/--
[rlc_leftRegion_eq_of_faceBoundaryTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWEulerianWinding.lean)
-/
@[path]
private lemma rlc_leftRegion_eq_of_faceBoundaryTrail_eq
  {K : Set (Site 2)}
  {f : Site 2}
  {c : (faceBoundaryGraph K).Walk f f}
-- given
  (hK : K.Finite)
  (htrail : c.IsTrail)
  (hcover : ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges) :
-- imply
  K = jec_leftRegion (c.mapLe (faceBoundaryGraph_le K)) := by
-- proof
  apply StatMech.Universality.rlc_leftRegion_eq_of_faceBoundaryTrail K hK c htrail hcover

/--
[rlc_exists_faceBoundaryTrail_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWEulerianWinding.lean)
-/
@[path]
private lemma rlc_exists_faceBoundaryTrail_leftRegion_eq_eq
  {K : Set (Site 2)}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (hx : x ∈ K)
  (hy : y ∉ K)
  (hin : ∀ a b : Site 2, a ∈ K → b ∈ K → (latticeMinusBarrier K).Reachable a b)
  (hout : ∀ a b : Site 2, a ∉ K → b ∉ K → (latticeMinusBarrier K).Reachable a b) :
-- imply
  ∃ (f : Site 2) (c : (faceBoundaryGraph K).Walk f f), c.IsTrail ∧ (∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ c.edges) ∧ K = jec_leftRegion (c.mapLe (faceBoundaryGraph_le K)) := by
-- proof
  apply StatMech.Universality.rlc_exists_faceBoundaryTrail_leftRegion_eq K hK hx hy hin hout


-- created on 2026-10-23
