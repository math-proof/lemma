import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
open StatMech StatMech.Universality


/--
[hexAWStart_mem_hexCSMids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexAWStart_mem_hexCSMids_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWStart ∈ hexCSMids T L := by
-- proof
  apply StatMech.Universality.hexAWStart_mem_hexCSMids T L hT

/--
[hexCSFiniteRegion_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSFiniteRegion_start_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hexCSFiniteRegion T L hT).start = hexAWStart := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_start T L hT

/--
[hexCSFiniteRegion_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSFiniteRegion_mids_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  (hexCSFiniteRegion T L hT).mids = hexCSMids T L := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_mids T L hT

/--
[hexCSMids_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSMids_reflect_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hz : z ∈ hexCSMids T L) :
-- imply
  hsc_refl hexAWStart 1 z ∈ hexCSMids T L := by
-- proof
  apply StatMech.Universality.hexCSMids_reflect hz

/--
[hexCSFiniteRegion_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSFiniteRegion_reflect_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hT : 0 < T)
  (hz : (hexCSFiniteRegion T L hT).inRegion z) :
-- imply
  (hexCSFiniteRegion T L hT).inRegion (hsc_refl hexAWStart 1 z) := by
-- proof
  apply StatMech.Universality.hexCSFiniteRegion_reflect hT z hz

/--
[hexCS_deterministic_winding_of_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_deterministic_winding_of_law_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L}
  {ts : List ℤ}
-- given
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (he : e ∈ hexCSBoundaryIncidences T L)
  (hne : e ≠ hexCSStartIncidence T L hT)
  (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ts).StaysIn (hexCSFiniteRegion T L hT).inRegion ∧ (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid e.vtx.1 e.edge)) :
-- imply
  (ofTurns hexAWStart 1 ts).turning = hexCSCanonicalWinding e := by
-- proof
  apply StatMech.Universality.hexCS_deterministic_winding_of_law hlaw e he hne ts hadm

/--
[hexCSInteriorMate_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_edge_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  (hexCSInteriorMate e).1.edge = e.1.edge := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_edge e

/--
[hexCSInteriorMate_vtx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_vtx_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  (hexCSInteriorMate e).1.vtx.1 = hexAWNeighbor e.1.vtx.1 e.1.edge := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_vtx e

/--
[hexCSInteriorMate_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_invol_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  hexCSInteriorMate (hexCSInteriorMate e) = e := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_invol e

/--
[hexCSInteriorMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_ne_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  hexCSInteriorMate e ≠ e := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_ne e

/--
[hexCSInteriorMate_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_mid_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  hexAWMid (hexCSInteriorMate e).1.vtx.1 (hexCSInteriorMate e).1.edge = hexAWMid e.1.vtx.1 e.1.edge := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_mid e

/--
[hexCSInteriorMate_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSInteriorMate_opposite_eq
  {T L : ℕ}
  {e : HexCSInteriorIncidence T L} :
-- imply
  hexAWMid (hexCSInteriorMate e).1.vtx.1 (hexCSInteriorMate e).1.edge - hexAWPos (hexCSInteriorMate e).1.vtx.1 = -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
-- proof
  apply StatMech.Universality.hexCSInteriorMate_opposite e

/--
[hexCSPairIncidence_eq_mate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSPairIncidence_eq_mate_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (he : hexCSIsInterior e) :
-- imply
  hexCSPairIncidence e = (hexCSInteriorMate ⟨e, he⟩).1 := by
-- proof
  apply StatMech.Universality.hexCSPairIncidence_eq_mate e he

/--
[hexCSDomainInteriorPairing_interior_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSDomainInteriorPairing_interior_sub_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT) :
-- imply
  (hexCSDomainInteriorPairing T L hT hlocal).interior ⊆ (hexCSDomain T L hT hlocal).incidences := by
-- proof
  apply StatMech.Universality.hexCSDomainInteriorPairing_interior_sub T L hT hlocal

/--
[hexCSDomain_incidences_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSDomain_incidences_eq_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT) :
-- imply
  (hexCSDomain T L hT hlocal).incidences = hexCSIncidences T L := by
-- proof
  apply StatMech.Universality.hexCSDomain_incidences_eq T L hT hlocal

/--
[hexCSIncidenceRank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSIncidenceRank_injective_eq
  {T L : ℕ} :
-- imply
  Function.Injective (@hexCSIncidenceRank T L) := by
-- proof
  apply StatMech.Universality.hexCSIncidenceRank_injective

/--
[hexCSPairIndex_ne_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSPairIndex_ne_reflect_eq
  {T L : ℕ}
  {i : HexCSPairIndex T L} :
-- imply
  i.1 ≠ hexCSReflectIncidence i.1 := by
-- proof
  apply StatMech.Universality.hexCSPairIndex_ne_reflect i

/--
[hexCSStartIncidence_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSStartIncidence_reflect_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSReflectIncidence (hexCSStartIncidence T L hT) = hexCSStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexCSStartIncidence_reflect T L hT

/--
[hexCS_mem_orbit_biUnion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_mem_orbit_biUnion_iff_eq
  {T L : ℕ}
  {e : HexCSIncidence T L}
-- given
  (hT : 0 < T) :
-- imply
  e ∈ Finset.univ.biUnion (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) ↔ e ∈ hexCSBoundaryIncidences T L ∧ e ≠ hexCSStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexCS_mem_orbit_biUnion_iff hT e

/--
[hexCS_boundary_orbit_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_boundary_orbit_partition_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSBoundaryIncidences T L = {hexCSStartIncidence T L hT} ∪ Finset.univ.biUnion (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
-- proof
  apply StatMech.Universality.hexCS_boundary_orbit_partition T L hT

/--
[hexCS_start_orbits_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_start_orbits_disjoint_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  Disjoint ({hexCSStartIncidence T L hT} : Finset (HexCSIncidence T L)) (Finset.univ.biUnion (hexCSOrbitPiece (T := T) (L := L) (hT := hT))) := by
-- proof
  apply StatMech.Universality.hexCS_start_orbits_disjoint T L hT

/--
[hexCS_orbitPieces_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_orbitPieces_pairwiseDisjoint_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  ((Finset.univ : Finset (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)) : Set (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)).PairwiseDisjoint (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
-- proof
  apply StatMech.Universality.hexCS_orbitPieces_pairwiseDisjoint T L hT

/--
[hexCSHeading_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSHeading_geometry_eq
  {T L : ℕ}
  {v : HexCSVertex T L}
  {e : Fin 3} :
-- imply
  hexAWMid v.1 e - hexAWPos v.1 = (1 / 2 : ℂ) * hexUnit (hexCSHeading v e) := by
-- proof
  apply StatMech.Universality.hexCSHeading_geometry v e

/--
[hexCSPairIndex_ne_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSPairIndex_ne_start_eq
  {T L : ℕ}
  {hT : 0 < T}
  {i : HexCSPairIndex T L} :
-- imply
  i.1 ≠ hexCSStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexCSPairIndex_ne_start i

/--
[hexCSReflectIncidence_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSReflectIncidence_mid_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexAWMid (hexCSReflectIncidence e).vtx.1 (hexCSReflectIncidence e).edge = hsc_refl hexAWStart 1 (hexAWMid e.vtx.1 e.edge) := by
-- proof
  apply StatMech.Universality.hexCSReflectIncidence_mid e

/--
[hexCSBoundaryPair_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSBoundaryPair_piece_eq
  {T L : ℕ}
  {i : HexCSPairIndex T L}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT) :
-- imply
  (hexCSBoundaryPair T L hT hlocal hlaw i).piece = hexCSPairPiece i := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPair_piece T L hT hlocal hlaw i

/--
[hexCSBoundaryPair_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSBoundaryPair_mass_nonneg_eq
  {T L : ℕ}
  {i : HexCSPairIndex T L}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT) :
-- imply
  0 ≤ (hexCSBoundaryPair T L hT hlocal hlaw i).mass := by
-- proof
  apply StatMech.Universality.hexCSBoundaryPair_mass_nonneg T L hT hlocal hlaw i

/--
[hexCSFixedIndex_heading_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSFixedIndex_heading_one_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexCSFixedIndex T L hT} :
-- imply
  hexCSCanonicalHeading k.1 = 1 := by
-- proof
  apply StatMech.Universality.hexCSFixedIndex_heading_one k

/--
[hexCSFixedIndex_winding_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSFixedIndex_winding_zero_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexCSFixedIndex T L hT} :
-- imply
  hexCSCanonicalWinding k.1 = 0 := by
-- proof
  apply StatMech.Universality.hexCSFixedIndex_winding_zero k

/--
[hexCSBoundaryFixed_piece](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCSBoundaryFixed_piece_eq
  {T L : ℕ}
  {k : HexCSFixedIndex T L hT}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT) :
-- imply
  (hexCSBoundaryFixed T L hT hlocal hlaw k).piece = hexCSFixedPiece k := by
-- proof
  apply StatMech.Universality.hexCSBoundaryFixed_piece T L hT hlocal hlaw k

/--
[endpointParafObservable_start_eq_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma endpointParafObservable_start_eq_one_of_unique_eq
  {R : HexFiniteRegion}
-- given
  (h0 : ℤ)
  (hunique : ∀ ts : List ℤ, (ofTurns R.start h0 ts).EndpointIsLegalSAW ∧ (ofTurns R.start h0 ts).StaysIn R.inRegion ∧ (ofTurns R.start h0 ts).EndsAt R.start → ts = []) :
-- imply
  endpointParafObservable R.inRegion R.start h0 R.start (5 / 8) hexChi = 1 := by
-- proof
  apply StatMech.Universality.endpointParafObservable_start_eq_one_of_unique R h0 hunique

/--
[hexCS_endpoint_normalized_dcs_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_endpoint_normalized_dcs_identity_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
-- proof
  apply StatMech.Universality.hexCS_endpoint_normalized_dcs_identity T L hT hlocal hlaw hstart

/--
[hexCS_dcsLam_eq_A](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_dcsLam_eq_A_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart H.dcsLam Kc = hexCSA T L hT := by
-- proof
  apply StatMech.Universality.hexCS_dcsLam_eq_A T L hT hlocal hlaw hstart

/--
[hexCS_dcsTau_eq_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_dcsTau_eq_E_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart H.dcsTau Kc = hexCSE T L hT := by
-- proof
  apply StatMech.Universality.hexCS_dcsTau_eq_E T L hT hlocal hlaw hstart

/--
[hexCS_dcsUps_eq_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_dcsUps_eq_B_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart H.dcsUps Kc = hexCSB T L hT := by
-- proof
  apply StatMech.Universality.hexCS_dcsUps_eq_B T L hT hlocal hlaw hstart

/--
[hexCS_finite_strip_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_finite_strip_identity_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  hexCl * hexCSA T L hT + hexCt * hexCSE T L hT + hexCSB T L hT = 1 := by
-- proof
  apply StatMech.Universality.hexCS_finite_strip_identity T L hT hlocal hlaw hstart

/--
[hexCS_boundary_masses_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean)
-/
@[path]
private lemma hexCS_boundary_masses_nonneg_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexCSLocalRelation T L hT)
  (hlaw : HexCSCanonicalWindingLaw T L hT)
  (hstart : HexCSStartReturnLaw T L hT) :
-- imply
  0 ≤ hexCSA T L hT ∧ 0 ≤ hexCSE T L hT ∧ 0 ≤ hexCSB T L hT := by
-- proof
  apply StatMech.Universality.hexCS_boundary_masses_nonneg T L hT hlocal hlaw hstart


-- created on 2026-10-23
