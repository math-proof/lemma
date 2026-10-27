import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jlri_sameRegion_along_offSupport_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_sameRegion_along_offSupport_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (x ∈ jec_leftRegion Vc ↔ y ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.jlri_sameRegion_along_offSupport_walk Vc p hp

/--
[jlri_leftRegion_bdEdge_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_leftRegion_bdEdge_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.jlri_leftRegion_bdEdge_support Vc hadj hbd

/--
[jlri_no_bdEdge_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_no_bdEdge_off_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Lattice.jlri_no_bdEdge_off_support Vc hadj hu hv

/--
[jlri_bdEdge_iff_endpoint_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_bdEdge_iff_endpoint_on_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) → (u ∈ Vc.support ∨ v ∈ Vc.support) := by
-- proof
  apply StatMech.Lattice.jlri_bdEdge_iff_endpoint_on_support Vc hadj

/--
[jlri_offSupport_adj_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_offSupport_adj_in_barrier_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Adj u v := by
-- proof
  apply StatMech.Lattice.jlri_offSupport_adj_in_barrier Vc hadj hu hv

/--
[jlri_offSupport_walk_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_offSupport_walk_in_barrier_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.jlri_offSupport_walk_in_barrier Vc p hp

/--
[jlri_inside_reachable_of_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_inside_reachable_of_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t := by
-- proof
  apply StatMech.Lattice.jlri_inside_reachable_of_offSupport Vc hInOff

/--
[jlri_outside_reachable_of_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_outside_reachable_of_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → (latticeMinusBarrier (jec_leftRegion Vc)).Reachable s t := by
-- proof
  apply StatMech.Lattice.jlri_outside_reachable_of_offSupport Vc hOutOff

/--
[jlri_two_components_of_offSupport_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_two_components_of_offSupport_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jlri_two_components_of_offSupport_connected Vc hp hq hInOff hOutOff

/--
[jlri_minimalLoop_sameRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_minimalLoop_sameRegion_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
-- imply
  (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.jlri_minimalLoop_sameRegion K a p hp

/--
[jlri_minimalLoop_no_bdEdge_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_minimalLoop_no_bdEdge_off_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ (mpl_orbitLoop K a).support)
  (hv : v ∉ (mpl_orbitLoop K a).support) :
-- imply
  ¬ bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(u, v) := by
-- proof
  apply StatMech.Lattice.jlri_minimalLoop_no_bdEdge_off_support K a hadj hu hv

/--
[jlri_minimalLoop_offSupport_walk_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_minimalLoop_offSupport_walk_in_barrier_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ (mpl_orbitLoop K a).support) :
-- imply
  (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).Reachable x y := by
-- proof
  apply StatMech.Lattice.jlri_minimalLoop_offSupport_walk_in_barrier K a p hp

/--
[jlri_minimalLoop_two_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanLeftRegionInterior.lean)
-/
@[path]
private lemma jlri_minimalLoop_two_components_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
  (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion (mpl_orbitLoop K a) → t ∈ jec_leftRegion (mpl_orbitLoop K a) → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support)
  (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion (mpl_orbitLoop K a) → t ∉ jec_leftRegion (mpl_orbitLoop K a) → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ (mpl_orbitLoop K a).support) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jlri_minimalLoop_two_components K a hp hq hInOff hOutOff


-- created on 2026-10-23
