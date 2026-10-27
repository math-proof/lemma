import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitSeparatesProof.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[osp_mem_windingRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_mem_windingRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  z ∈ osp_windingRegion K hK e he ↔ ¬ Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.osp_mem_windingRegion K hK e he z

/--
[osp_orbitSeparates_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitSeparates_of_residues_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hF1 : OrbitWindsBdEdge K hK e he)
  (hF2 : OrbitFillsWinding K hK e he) :
-- imply
  OrbitSeparates K e := by
-- proof
  apply StatMech.Lattice.osp_orbitSeparates_of_residues K hK e he hF1 hF2

/--
[osp_orbitWindsBdEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitWindsBdEdge_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  OrbitWindsBdEdge K hK e he ↔ (e.tail ∈ osp_windingRegion K hK e he ↔ e.head ∉ osp_windingRegion K hK e he) := by
-- proof
  apply StatMech.Lattice.osp_orbitWindsBdEdge_iff K hK e he

/--
[osp_orbitEdge_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitEdge_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (h : IsOrbitEdge K e x y) :
-- imply
  bdEdge K s(x, y) := by
-- proof
  apply StatMech.Lattice.osp_orbitEdge_bdEdge K e he h

/--
[osp_fillsWinding_endpoint_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_fillsWinding_endpoint_face_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj x y)
  (hbd : bdEdge (osp_windingRegion K hK e he) s(x, y)) :
-- imply
  x ∈ (olb_orbitLoop K hK e he).support ∨ y ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Lattice.osp_fillsWinding_endpoint_face K hK e he hadj hbd

/--
[osp_singleton_orbitEdge_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_singleton_orbitEdge_endpoint_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2}
  {e : Dart}
  {x y : Site 2}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e)
  (h : IsOrbitEdge ({c} : Set (Site 2)) e x y) :
-- imply
  x = c ∨ y = c := by
-- proof
  apply StatMech.Lattice.osp_singleton_orbitEdge_endpoint c e he h

/--
[osp_singleton_posAxisEdge_isOrbitEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_singleton_posAxisEdge_isOrbitEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) := by
-- proof
  apply StatMech.Lattice.osp_singleton_posAxisEdge_isOrbitEdge c e he

/--
[osp_singleton_orbitEdges_not_even_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_singleton_orbitEdges_not_even_degree_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {c : Site 2}
  {e : Dart}
-- given
  (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
-- imply
  IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) ∧ (∀ y : Site 2, IsOrbitEdge ({c} : Set (Site 2)) e (c + ![1, 0]) y → y = c) := by
-- proof
  apply StatMech.Lattice.osp_singleton_orbitEdges_not_even_degree c e he

/--
[osp_orbitWindsBdEdge_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitWindsBdEdge_of_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
-- imply
  OrbitWindsBdEdge K hK e he := by
-- proof
  apply StatMech.Lattice.osp_orbitWindsBdEdge_of_match K hK e he hmatch

/--
[osp_orbitFillsWinding_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitFillsWinding_of_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitFillsWinding K hK e he := by
-- proof
  apply StatMech.Lattice.osp_orbitFillsWinding_of_match K hK e he hmatch hcov

/--
[osp_orbitSeparates_of_match_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_orbitSeparates_of_match_cover_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitSeparates K e := by
-- proof
  apply StatMech.Lattice.osp_orbitSeparates_of_match_cover K hK e he hmatch hcov

/--
[osp_traceSurjective_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_traceSurjective_of_residues_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
  (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he) :
-- imply
  OrbitTraceSurjective (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.osp_traceSurjective_of_residues hfin hF1 hF2

/--
[osp_interfaceConnected_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_interfaceConnected_of_residues_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
  (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he) :
-- imply
  InterfaceConnected (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.osp_interfaceConnected_of_residues hfin hF1 hF2

/--
[osp_exitDartsSameOrbit_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_exitDartsSameOrbit_of_residues_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
  (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he)
  (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
  (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
  (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
-- imply
  ExitDartsSameOrbit ω hfin := by
-- proof
  apply StatMech.Lattice.osp_exitDartsSameOrbit_of_residues hfin hF1 hF2 R hR hr hl

/--
[osp_pc_lt_one_of_residues_and_links](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitSeparatesProof.lean)
-/
@[path]
private lemma osp_pc_lt_one_of_residues_and_links_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.osp_pc_lt_one_of_residues_and_links h


-- created on 2026-10-23
