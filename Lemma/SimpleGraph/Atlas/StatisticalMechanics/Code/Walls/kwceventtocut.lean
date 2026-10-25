import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
open Finset SimpleGraph StatMech StatMech.Walls


/--
[kwc_crossEdge_symm_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_crossEdge_symm_eq_map_eq
  {e : Sym2 (Site 2)} :
-- imply
  crossEdge.symm e = Sym2.map rot90Inv e := by
-- proof
  apply StatMech.Walls.kwc_crossEdge_symm_eq_map e

/--
[kwc_rot90Iso_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_rot90Iso_symm_apply_eq
  {x : Site 2} :
-- imply
  rot90Iso.symm x = rot90Inv x := by
-- proof
  apply StatMech.Walls.kwc_rot90Iso_symm_apply x

/--
[kwc_mapped_walk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_mapped_walk_edges_eq
  {w : Site 2}
  {W : (hypercubicLattice 2).Walk w w} :
-- imply
  (W.map rot90Iso.symm.toHom).edges = W.edges.map crossEdge.symm := by
-- proof
  apply StatMech.Walls.kwc_mapped_walk_edges W

/--
[kwc_pullback_eq_mapped_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_pullback_eq_mapped_edges_eq
  {w : Site 2}
  {W : (hypercubicLattice 2).Walk w w} :
-- imply
  (W.edges.toFinset).image crossEdge.symm = (W.map rot90Iso.symm.toHom).edges.toFinset := by
-- proof
  apply StatMech.Walls.kwc_pullback_eq_mapped_edges W

/--
[kwc_latticeDualWalkHasBdEdgeRegion_of_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_latticeDualWalkHasBdEdgeRegion_of_primal_eq
-- given
  (hprimal : PrimalWalkBoundsRegion) :
-- imply
  LatticeDualWalkHasBdEdgeRegion (hypercubicLattice 2) := by
-- proof
  apply StatMech.Walls.kwc_latticeDualWalkHasBdEdgeRegion_of_primal hprimal

/--
[kwc_dualWalkBoundsRegion_of_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_dualWalkBoundsRegion_of_primal_eq
-- given
  (hprimal : PrimalWalkBoundsRegion) :
-- imply
  DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge := by
-- proof
  apply StatMech.Walls.kwc_dualWalkBoundsRegion_of_primal hprimal

/--
[kwc_primalWalkBoundsRegion_of_leftRegionMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_primalWalkBoundsRegion_of_leftRegionMatch_eq
-- given
  (hmatch : kwc_PrimalWalkLeftRegionMatch) :
-- imply
  PrimalWalkBoundsRegion := by
-- proof
  apply StatMech.Walls.kwc_primalWalkBoundsRegion_of_leftRegionMatch hmatch

/--
[kwc_leftRegion_bdEdge_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_leftRegion_bdEdge_incident_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.kwc_leftRegion_bdEdge_incident Vc hadj hbd

/--
[kwc_primalWalkBoundsRegion_nil_case](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean)
-/
@[path]
private lemma kwc_primalWalkBoundsRegion_nil_case_eq
  {a : Site 2} :
-- imply
  ∃ S : Set (Site 2), ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges.toFinset ↔ bdEdge S s(u, v)) := by
-- proof
  apply StatMech.Walls.kwc_primalWalkBoundsRegion_nil_case


-- created on 2026-10-23
