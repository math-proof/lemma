import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
open SimpleGraph Function StatMech StatMech.Lattice


/--
[ifg_dartNext_head_kingReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_dartNext_head_kingReachable_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨(dartNext K e).head, (dartNext_isBoundaryDart K e he).2⟩ := by
-- proof
  apply StatMech.Lattice.ifg_dartNext_head_kingReachable K e he

/--
[ifg_iterate_head_kingReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_iterate_head_kingReachable_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨((dartNext K)^[n] e).head, (iterate_isBoundaryDart' K e he n).2⟩ := by
-- proof
  apply StatMech.Lattice.ifg_iterate_head_kingReachable K e he n

/--
[ifg_orbit_kingReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_orbit_kingReachable_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (h : SameOrbit K e f) :
-- imply
  (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
-- proof
  apply StatMech.Lattice.ifg_orbit_kingReachable K he hf h

/--
[orbitTraceSurjective_iff_interfaceConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma orbitTraceSurjective_iff_interfaceConnected_eq
  {K : Set (Site 2)} :
-- imply
  OrbitTraceSurjective K ↔ InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.orbitTraceSurjective_iff_interfaceConnected K

/--
[ifg_orbitTraceSurjective_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_orbitTraceSurjective_singleton_eq
  {c : Site 2} :
-- imply
  OrbitTraceSurjective ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.ifg_orbitTraceSurjective_singleton c

/--
[ifg_boundaryKingConnected_of_clusterConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_boundaryKingConnected_of_clusterConnected_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (hsurj : OrbitTraceSurjective K)
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩) :
-- imply
  SameOrbit K e f ∧ (boundaryKingGraph K).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
-- proof
  apply StatMech.Lattice.ifg_boundaryKingConnected_of_clusterConnected K hsurj he hf hcomp

/--
[ifg_no_facingDart_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_no_facingDart_singleton_eq
  {c v : Site 2}
  {d : Dart}
-- given
  (hv : unitWt (v - c) ≠ 1)
  (hd : IsBoundaryDart ({c} : Set (Site 2)) d) :
-- imply
  d.head ≠ v := by
-- proof
  apply StatMech.Lattice.ifg_no_facingDart_singleton c v hv d hd

/--
[ifg_not_orbitReached_two_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_not_orbitReached_two_zero_eq
  {e : Dart} :
-- imply
  ¬ OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![2, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.ifg_not_orbitReached_two_zero e

/--
[ifg_not_orbitKingTransport_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedGlobal.lean)
-/
@[path]
private lemma ifg_not_orbitKingTransport_singleton_eq :
-- imply
  ¬ OrbitKingTransport ({(0 : Site 2)} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.ifg_not_orbitKingTransport_singleton


-- created on 2026-10-23
