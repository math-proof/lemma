import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitFillsWindingProof
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ofw_orbitEdge_one_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitEdge_one_in_K_eq
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
  apply StatMech.Lattice.ofw_orbitEdge_one_in_K K e he h

/--
[ofw_orbitEdge_bdEdge_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitEdge_bdEdge_K_eq
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
  apply StatMech.Lattice.ofw_orbitEdge_bdEdge_K K e he h

/--
[ofw_localConstancy_gives_support_only](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_localConstancy_gives_support_only_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj x y)
  (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(x, y)) :
-- imply
  x ∈ (olb_orbitLoop K hK e he).support ∨ y ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Lattice.ofw_localConstancy_gives_support_only K hK e he hadj hbd

/--
[ofw_loopFaceEdge_not_orbitEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_loopFaceEdge_not_orbitEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {f g : Site 2}
-- given
  (he : IsBoundaryDart K e)
  (hf : f ∉ K)
  (hg : g ∉ K) :
-- imply
  ¬ IsOrbitEdge K e f g := by
-- proof
  apply StatMech.Lattice.ofw_loopFaceEdge_not_orbitEdge K e he hf hg

/--
[ofw_orbitFillsWinding_of_revMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitFillsWinding_of_revMatch_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hrev : OrbitWindingRevMatch K hK e he)
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitFillsWinding K hK e he := by
-- proof
  apply StatMech.Lattice.ofw_orbitFillsWinding_of_revMatch K hK e he hrev hcov

/--
[ofw_revMatch_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_revMatch_of_match_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
-- imply
  OrbitWindingRevMatch K hK e he := by
-- proof
  apply StatMech.Lattice.ofw_revMatch_of_match K hK e he hmatch

/--
[ofw_orbitFillsWinding_iff_via_coverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitFillsWinding_iff_via_coverage_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitFillsWinding K hK e he ↔ OrbitWindingRevMatch K hK e he := by
-- proof
  apply StatMech.Lattice.ofw_orbitFillsWinding_iff_via_coverage K hK e he hcov

/--
[ofw_orbitWindsBdEdge_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitWindsBdEdge_of_match_eq
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
  apply StatMech.Lattice.ofw_orbitWindsBdEdge_of_match K hK e he hmatch

/--
[ofw_orbitSeparates_of_revMatch_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_orbitSeparates_of_revMatch_cover_eq
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
  apply StatMech.Lattice.ofw_orbitSeparates_of_revMatch_cover K hK e he hmatch hcov

/--
[ofw_traceSurjective_of_revMatch_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_traceSurjective_of_revMatch_cover_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hmatch : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), pww_BdEdgeMatch (cluster 2 ω (origin 2)) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
  (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e → OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
-- imply
  OrbitTraceSurjective (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.ofw_traceSurjective_of_revMatch_cover hfin hmatch hcov

/--
[ofw_pc_lt_one_of_residues_and_links](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean)
-/
@[path]
private lemma ofw_pc_lt_one_of_residues_and_links_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.ofw_pc_lt_one_of_residues_and_links h


-- created on 2026-10-23
