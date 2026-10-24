import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[icb_orbitReached_straight_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_orbitReached_straight_step_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e d : Dart}
-- given
  (hd : IsBoundaryDart K d)
  (hsame : SameOrbit K e d)
  (hfront : d.head + (-rot90Fun d.dir) ∉ K)
  (hside : d.tail + (-rot90Fun d.dir) ∈ K) :
-- imply
  OrbitReached K e (d.head + (-rot90Fun d.dir)) := by
-- proof
  apply StatMech.Lattice.icb_orbitReached_straight_step K e d hd hsame hfront hside

/--
[icb_orbitReached_corner_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_orbitReached_corner_step_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e d : Dart}
-- given
  (hd : IsBoundaryDart K d)
  (hsame : SameOrbit K e d)
  (hfront : d.head + (-rot90Fun d.dir) ∉ K)
  (hside : d.tail + (-rot90Fun d.dir) ∉ K) :
-- imply
  OrbitReached K e (d.tail + (-rot90Fun d.dir)) := by
-- proof
  apply StatMech.Lattice.icb_orbitReached_corner_step K e d hd hsame hfront hside

/--
[icb_orbitReached_wallStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_orbitReached_wallStep_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e d : Dart}
-- given
  (hd : IsBoundaryDart K d)
  (hsame : SameOrbit K e d) :
-- imply
  OrbitReached K e (dartNext K d).head ∧ ((dartNext K d).head = d.head ∨ KingAdj d.head (dartNext K d).head) := by
-- proof
  apply StatMech.Lattice.icb_orbitReached_wallStep K e d hd hsame

/--
[icb_orbitReached_of_complReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_orbitReached_of_complReachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {u w : Site 2}
-- given
  (htr : UnitEdgeOrbitTransport K)
  (he : IsBoundaryDart K e)
  (hu : u ∉ K)
  (hw : w ∉ K)
  (hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
  (hou : OrbitReached K e u) :
-- imply
  OrbitReached K e w := by
-- proof
  apply StatMech.Lattice.icb_orbitReached_of_complReachable K htr e he hu hw hreach hou

/--
[icb_interfaceConnected_of_unitEdgeTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_interfaceConnected_of_unitEdgeTransport_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
-- given
  (htr : UnitEdgeOrbitTransport K)
  (hsat : OrbitVertexSaturate K) :
-- imply
  InterfaceConnected K := by
-- proof
  apply StatMech.Lattice.icb_interfaceConnected_of_unitEdgeTransport K htr hsat

/--
[icb_unitEdgeTransport_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_unitEdgeTransport_false_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ¬ UnitEdgeOrbitTransport ({(0 : Site 2)} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.icb_unitEdgeTransport_false

/--
[icb_interfaceConnected_iff_traceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_interfaceConnected_iff_traceSurjective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)} :
-- imply
  InterfaceConnected K ↔ OrbitTraceSurjective K := by
-- proof
  apply StatMech.Lattice.icb_interfaceConnected_iff_traceSurjective K

/--
[icb_traceSurjective_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_traceSurjective_singleton_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2} :
-- imply
  OrbitTraceSurjective ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.icb_traceSurjective_singleton c

/--
[icb_sameOrbit_imp_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_sameOrbit_imp_sameComponent_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (h : SameOrbit K e f) :
-- imply
  ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨e.head, he.2⟩ ⟨f.head, hf.2⟩ := by
-- proof
  apply StatMech.Lattice.icb_sameOrbit_imp_sameComponent K he hf h

/--
[icb_exitHeads_reachable_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_exitHeads_reachable_of_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩ ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩ := by
-- proof
  apply StatMech.Lattice.icb_exitHeads_reachable_of_far hfin R hR hr hl

/--
[icb_exitDartsSameOrbit_of_traceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_exitDartsSameOrbit_of_traceSurjective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsurj : OrbitTraceSurjective (cluster 2 ω (origin 2)))
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.icb_exitDartsSameOrbit_of_traceSurjective hfin hsurj R hR hr hl

/--
[icb_exitFaces_reachable_of_traceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_exitFaces_reachable_of_traceSurjective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsurj : OrbitTraceSurjective (cluster 2 ω (origin 2)))
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.icb_exitFaces_reachable_of_traceSurjective hfin hsurj R hR hr hl

/--
[icb_pc_lt_one_via_traceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnectedBuild.lean)
-/
@[path]
private lemma icb_pc_lt_one_via_traceSurjective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.icb_pc_lt_one_via_traceSurjective h


-- created on 2026-10-23
