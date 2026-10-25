import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[obs_isOrbitEdge_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_isOrbitEdge_symm_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (h : IsOrbitEdge K e x y) :
-- imply
  IsOrbitEdge K e y x := by
-- proof
  apply StatMech.Lattice.obs_isOrbitEdge_symm K e h

/--
[latticeMinusOrbit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma latticeMinusOrbit_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2} :
-- imply
  (latticeMinusOrbit K e).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y := by
-- proof
  apply StatMech.Lattice.latticeMinusOrbit_adj K e x y

/--
[obs_orbitEdge_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitEdge_isBoundaryDart_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (h : IsOrbitEdge K e x y) :
-- imply
  ∃ d : Dart, IsBoundaryDart K d ∧ SameOrbit K e d ∧ ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x)) := by
-- proof
  apply StatMech.Lattice.obs_orbitEdge_isBoundaryDart K e he h

/--
[obs_orbitEdge_one_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitEdge_one_in_K_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (h : IsOrbitEdge K e x y) :
-- imply
  (x ∈ K ↔ y ∉ K) := by
-- proof
  apply StatMech.Lattice.obs_orbitEdge_one_in_K K e he h

/--
[obs_not_orbitEdge_of_both_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_not_orbitEdge_of_both_in_K_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (hx : x ∈ K)
  (hy : y ∈ K) :
-- imply
  ¬ IsOrbitEdge K e x y := by
-- proof
  apply StatMech.Lattice.obs_not_orbitEdge_of_both_in_K K e he hx hy

/--
[obs_not_orbitEdge_of_both_not_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_not_orbitEdge_of_both_not_in_K_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (hx : x ∉ K)
  (hy : y ∉ K) :
-- imply
  ¬ IsOrbitEdge K e x y := by
-- proof
  apply StatMech.Lattice.obs_not_orbitEdge_of_both_not_in_K K e he hx hy

/--
[obs_orbitReachable_of_complReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitReachable_of_complReachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {u w : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (hu : u ∉ K)
  (hw : w ∉ K)
  (h : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩) :
-- imply
  (latticeMinusOrbit K e).Reachable u w := by
-- proof
  apply StatMech.Lattice.obs_orbitReachable_of_complReachable K e he hu hw h

/--
[obs_orbitReachable_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitReachable_of_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart (cluster 2 ω o) e)
  (hx : x ∈ cluster 2 ω o)
  (hxy : Connected 2 ω x y) :
-- imply
  (latticeMinusOrbit (cluster 2 ω o) e).Reachable x y := by
-- proof
  apply StatMech.Lattice.obs_orbitReachable_of_connected o e he hx hxy

/--
[obs_sameOrbit_of_orbitEdge_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_sameOrbit_of_orbitEdge_boundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (h : IsOrbitEdge K e f.tail f.head) :
-- imply
  SameOrbit K e f := by
-- proof
  apply StatMech.Lattice.obs_sameOrbit_of_orbitEdge_boundary K e f he hf h

/--
[obs_traceSurjective_of_orbitSeparates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_traceSurjective_of_orbitSeparates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
-- imply
  OrbitTraceSurjective (cluster 2 ω o) := by
-- proof
  apply StatMech.Lattice.obs_traceSurjective_of_orbitSeparates o hsep

/--
[obs_interfaceConnected_of_orbitSeparates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_interfaceConnected_of_orbitSeparates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
-- imply
  InterfaceConnected (cluster 2 ω o) := by
-- proof
  apply StatMech.Lattice.obs_interfaceConnected_of_orbitSeparates o hsep

/--
[obs_latticeMinusOrbit_le_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_latticeMinusOrbit_le_barrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  latticeMinusOrbit K e ≤ latticeMinusBarrier K := by
-- proof
  apply StatMech.Lattice.obs_latticeMinusOrbit_le_barrier K e hcov

/--
[obs_orbitSeparates_of_coversBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitSeparates_of_coversBoundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitSeparates K e := by
-- proof
  apply StatMech.Lattice.obs_orbitSeparates_of_coversBoundary K e he hcov

/--
[obs_orbitCoversBoundaryEdges_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitCoversBoundaryEdges_singleton_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  OrbitCoversBoundaryEdges ({c} : Set (Site 2)) e := by
-- proof
  apply StatMech.Lattice.obs_orbitCoversBoundaryEdges_singleton c e he

/--
[obs_orbitSeparates_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_orbitSeparates_singleton_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  OrbitSeparates ({c} : Set (Site 2)) e := by
-- proof
  apply StatMech.Lattice.obs_orbitSeparates_singleton c e he

/--
[obs_exitDartsSameOrbit_of_orbitSeparates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_exitDartsSameOrbit_of_orbitSeparates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω (origin 2)) e → OrbitSeparates (cluster 2 ω (origin 2)) e)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.obs_exitDartsSameOrbit_of_orbitSeparates hfin hsep R hR hr hl

/--
[obs_pc_lt_one_of_orbitSeparates_and_links](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean)
-/
@[path]
private lemma obs_pc_lt_one_of_orbitSeparates_and_links_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.obs_pc_lt_one_of_orbitSeparates_and_links h


-- created on 2026-10-23
