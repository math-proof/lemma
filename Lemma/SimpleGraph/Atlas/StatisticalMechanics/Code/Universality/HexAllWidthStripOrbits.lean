import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
open StatMech StatMech.Universality


/--
[hexAWDomain_interiorVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomain_interiorVertices_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomain T L hT hlocal).interiorVertices = Finset.univ := by
-- proof
  apply StatMech.Universality.hexAWDomain_interiorVertices T L hT hlocal

/--
[hexAWDomain_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomain_pos_eq
  {T L : ℕ}
  {v : HexAWVertex T L}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomain T L hT hlocal).pos v = hexAWPos v.1 := by
-- proof
  apply StatMech.Universality.hexAWDomain_pos T L hT hlocal v

/--
[hexAWDomain_mid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomain_mid_eq
  {T L : ℕ}
  {v : HexAWVertex T L}
  {j : Fin 3}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomain T L hT hlocal).mid v j = hexAWMid v.1 j := by
-- proof
  apply StatMech.Universality.hexAWDomain_mid T L hT hlocal v j

/--
[hexAWDomain_obs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomain_obs_eq
  {T L : ℕ}
  {z : ℂ}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomain T L hT hlocal).obs z = hexAWObservable T L hT z := by
-- proof
  apply StatMech.Universality.hexAWDomain_obs T L hT hlocal z

/--
[hexAWDomainInteriorPairing_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomainInteriorPairing_interior_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomainInteriorPairing T L hT hlocal).interior = hexAWInteriorIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWDomainInteriorPairing_interior T L hT hlocal

/--
[hexAWDomainInteriorPairing_interior_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWDomainInteriorPairing_interior_sub_eq
  {T L : ℕ}
-- given
  (hT : 0 < T)
  (hlocal : HexAWLocalRelation T L hT) :
-- imply
  (hexAWDomainInteriorPairing T L hT hlocal).interior ⊆ (hexAWDomain T L hT hlocal).incidences := by
-- proof
  apply StatMech.Universality.hexAWDomainInteriorPairing_interior_sub T L hT hlocal

/--
[hexAWIncidenceRank_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWIncidenceRank_injective_eq
  {T L : ℕ} :
-- imply
  Function.Injective (@hexAWIncidenceRank T L) := by
-- proof
  apply StatMech.Universality.hexAWIncidenceRank_injective

/--
[hexAWOrbitPiece_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWOrbitPiece_eq_raw_eq
  {T L : ℕ}
  {hT : 0 < T} :
-- imply
  (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) = fun o : HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT => match o with := by
-- proof
  apply StatMech.Universality.hexAWOrbitPiece_eq_raw

/--
[hexAWPairIndex_ne_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWPairIndex_ne_reflect_eq
  {T L : ℕ}
  {i : HexAWPairIndex T L} :
-- imply
  i.1 ≠ hexAWReflectIncidence i.1 := by
-- proof
  apply StatMech.Universality.hexAWPairIndex_ne_reflect i

/--
[hexAWPairIndex_reflect_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWPairIndex_reflect_mem_boundary_eq
  {T L : ℕ}
  {i : HexAWPairIndex T L} :
-- imply
  hexAWReflectIncidence i.1 ∈ hexAWBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWPairIndex_reflect_mem_boundary i

/--
[hexAWPairPiece_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWPairPiece_mem_boundary_eq
  {T L : ℕ}
  {i : HexAWPairIndex T L}
  {e : HexAWIncidence T L}
-- given
  (he : e ∈ hexAWPairPiece i) :
-- imply
  e ∈ hexAWBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWPairPiece_mem_boundary i he

/--
[hexAWPairPiece_not_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWPairPiece_not_start_eq
  {T L : ℕ}
  {i : HexAWPairIndex T L}
  {e : HexAWIncidence T L}
-- given
  (hT : 0 < T)
  (he : e ∈ hexAWPairPiece i) :
-- imply
  e ≠ hexAWStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexAWPairPiece_not_start hT i he

/--
[hexAWFixedPiece_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWFixedPiece_mem_boundary_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexAWFixedIndex T L hT}
  {e : HexAWIncidence T L}
-- given
  (he : e ∈ hexAWFixedPiece k) :
-- imply
  e ∈ hexAWBoundaryIncidences T L := by
-- proof
  apply StatMech.Universality.hexAWFixedPiece_mem_boundary k he

/--
[hexAWFixedPiece_not_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWFixedPiece_not_start_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexAWFixedIndex T L hT}
  {e : HexAWIncidence T L}
-- given
  (he : e ∈ hexAWFixedPiece k) :
-- imply
  e ≠ hexAWStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexAWFixedPiece_not_start k he

/--
[hexAW_mem_orbit_biUnion_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAW_mem_orbit_biUnion_iff_eq
  {T L : ℕ}
  {e : HexAWIncidence T L}
-- given
  (hT : 0 < T) :
-- imply
  e ∈ (Finset.univ.biUnion (hexAWOrbitPiece (T := T) (L := L) (hT := hT))) ↔ e ∈ hexAWBoundaryIncidences T L ∧ e ≠ hexAWStartIncidence T L hT := by
-- proof
  apply StatMech.Universality.hexAW_mem_orbit_biUnion_iff hT e

/--
[hexAW_boundary_orbit_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAW_boundary_orbit_partition_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexAWBoundaryIncidences T L = {hexAWStartIncidence T L hT} ∪ Finset.univ.biUnion (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) := by
-- proof
  apply StatMech.Universality.hexAW_boundary_orbit_partition T L hT

/--
[hexAW_start_orbits_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAW_start_orbits_disjoint_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  Disjoint ({hexAWStartIncidence T L hT} : Finset (HexAWIncidence T L)) (Finset.univ.biUnion (hexAWOrbitPiece (T := T) (L := L) (hT := hT))) := by
-- proof
  apply StatMech.Universality.hexAW_start_orbits_disjoint T L hT

/--
[hexAW_orbitPieces_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAW_orbitPieces_pairwiseDisjoint_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  ((Finset.univ : Finset (HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT)) : Set (HexAWPairIndex T L ⊕ HexAWFixedIndex T L hT)).PairwiseDisjoint (hexAWOrbitPiece (T := T) (L := L) (hT := hT)) := by
-- proof
  apply StatMech.Universality.hexAW_orbitPieces_pairwiseDisjoint T L hT

/--
[hexAWFixedIndex_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWFixedIndex_eq_right_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexAWFixedIndex T L hT} :
-- imply
  ∃ n : ℕ, 0 < n ∧ T = 2 * n ∧ k.1.vtx.1 = hexAWRightFixedCoord n ∧ k.1.edge = 0 := by
-- proof
  apply StatMech.Universality.hexAWFixedIndex_eq_right k

/--
[hexAWFixedIndex_isEmpty_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWFixedIndex_isEmpty_of_odd_eq
  {T L : ℕ}
  {hT : 0 < T}
-- given
  (hodd : Odd T) :
-- imply
  IsEmpty (HexAWFixedIndex T L hT) := by
-- proof
  apply StatMech.Universality.hexAWFixedIndex_isEmpty_of_odd hodd

/--
[hexAWFixedIndex_subsingleton_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean)
-/
@[path]
private lemma hexAWFixedIndex_subsingleton_even_eq
  {n L : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  ∀ k : HexAWFixedIndex (2 * n) L (by omega), k = hexAWRightFixedIndex n L hn := by
-- proof
  apply StatMech.Universality.hexAWFixedIndex_subsingleton_even n L hn


-- created on 2026-10-23
