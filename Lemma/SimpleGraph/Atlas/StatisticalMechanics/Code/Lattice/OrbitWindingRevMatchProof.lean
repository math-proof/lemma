import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingRevMatchProof
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[owr_leftRegion_subset_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_leftRegion_subset_of_exterior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
-- imply
  jec_leftRegion (olb_orbitLoop K hK e he) ⊆ K := by
-- proof
  apply StatMech.Lattice.owr_leftRegion_subset_of_exterior K hK e he hExt

/--
[owr_revMatch_of_subset_and_noCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_revMatch_of_subset_and_noCross_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hsub : jec_leftRegion Vc ⊆ K)
  (hnoCross : ∀ x y : Site 2, (hypercubicLattice 2).Adj x y → x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc) :
-- imply
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y → bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) := by
-- proof
  apply StatMech.Lattice.owr_revMatch_of_subset_and_noCross K Vc hsub hnoCross

/--
[owr_noCross_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_noCross_of_interior_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hKsub : K ⊆ jec_leftRegion Vc) :
-- imply
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y → x ∈ jec_leftRegion Vc → y ∈ K → y ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.owr_noCross_of_interior K Vc hKsub

/--
[owr_revMatch_of_inclusions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_revMatch_of_inclusions_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hsub : jec_leftRegion Vc ⊆ K)
  (hKsub : K ⊆ jec_leftRegion Vc) :
-- imply
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y → bdEdge (jec_leftRegion Vc) s(x, y) → bdEdge K s(x, y) := by
-- proof
  apply StatMech.Lattice.owr_revMatch_of_inclusions K Vc hsub hKsub

/--
[owr_revMatch_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_revMatch_of_winding_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
  (hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
-- imply
  OrbitWindingRevMatch K hK e he := by
-- proof
  apply StatMech.Lattice.owr_revMatch_of_winding K hK e he hExt hz0K hodd0 hInt

/--
[owr_revMatch_of_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_revMatch_of_match_eq
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
  apply StatMech.Lattice.owr_revMatch_of_match K hK e he hmatch

/--
[owr_revMatch_of_interiorInclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_revMatch_of_interiorInclusion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
  (hKsub : K ⊆ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  OrbitWindingRevMatch K hK e he := by
-- proof
  apply StatMech.Lattice.owr_revMatch_of_interiorInclusion K hK e he hExt hKsub

/--
[owr_orbitSeparates_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_orbitSeparates_of_winding_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
  (hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support))
  (hcov : OrbitCoversBoundaryEdges K e) :
-- imply
  OrbitSeparates K e := by
-- proof
  apply StatMech.Lattice.owr_orbitSeparates_of_winding K hK e he hExt hz0K hodd0 hInt hcov

/--
[owr_traceSurjective_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_traceSurjective_of_winding_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hExt : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧ (∀ q ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ q 0))
  (hwit : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e), ∃ z0 : Site 2, z0 ∈ cluster 2 ω (origin 2) ∧ ¬ Even (jec_rayCount z0 (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)) ∧ ∀ z, z ∈ cluster 2 ω (origin 2) → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support))
  (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e → OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
-- imply
  OrbitTraceSurjective (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.owr_traceSurjective_of_winding hfin hExt hwit hcov

/--
[owr_pc_lt_one_of_residues_and_links](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitWindingRevMatchProof.lean)
-/
@[path]
private lemma owr_pc_lt_one_of_residues_and_links_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), EnclosingContourLinksExits ω hfin) :
-- imply
  StatMech.Percolation.pc 2 < 1 := by
-- proof
  apply StatMech.Lattice.owr_pc_lt_one_of_residues_and_links h


-- created on 2026-10-23
