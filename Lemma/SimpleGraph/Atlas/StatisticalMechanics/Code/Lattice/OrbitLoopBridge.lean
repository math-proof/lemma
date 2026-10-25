import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[olb_orbitLoop_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_support_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (olb_orbitLoop K hK e he).support = (dartOrbitFaceLoop K hK e he).support := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_support K hK e he

/--
[olb_orbitLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_edges_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (olb_orbitLoop K hK e he).edges = (dartOrbitFaceLoop K hK e he).edges := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_edges K hK e he

/--
[olb_orbitLoop_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_length_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (olb_orbitLoop K hK e he).length = (dartOrbitFaceLoop K hK e he).length := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_length K hK e he

/--
[olb_orbitLoop_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_length_pos_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  0 < (olb_orbitLoop K hK e he).length := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_length_pos K hK e he

/--
[olb_orbitLoop_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_ne_nil_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  olb_orbitLoop K hK e he ≠ SimpleGraph.Walk.nil := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_ne_nil K hK e he

/--
[olb_orbitLoop_edges_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_edges_bdEdge_eq
  {K : Set (Site 2)}
  {e : Dart}
  {f g : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (h : s(f, g) ∈ (olb_orbitLoop K hK e he).edges) :
-- imply
  bdEdge K (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_edges_bdEdge K hK e he h

/--
[olb_orbitLoop_crossCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbitLoop_crossCount_even_eq
  {K : Set (Site 2)}
  {e : Dart}
  {S : Set (Site 2)}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  Even (crossCount S (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.olb_orbitLoop_crossCount_even K hK e he S

/--
[olb_orbit_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbit_separation_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (olb_orbitLoop K hK e he).support)
  (hv : v ∉ (olb_orbitLoop K hK e he).support) :
-- imply
  (Even (jec_rayCount u (olb_orbitLoop K hK e he)) ↔ Even (jec_rayCount v (olb_orbitLoop K hK e he))) := by
-- proof
  apply StatMech.Lattice.olb_orbit_separation K hK e he hadj hu hv

/--
[olb_orbit_leftRegion_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitLoopBridge.lean)
-/
@[path]
private lemma olb_orbit_leftRegion_bdEdge_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
-- imply
  u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Lattice.olb_orbit_leftRegion_bdEdge K hK e he hadj hbd


-- created on 2026-10-23
