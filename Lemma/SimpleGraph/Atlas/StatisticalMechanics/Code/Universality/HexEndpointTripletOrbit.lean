import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointTripletOrbit
open StatMech StatMech.Universality


/--
[specialMidCount_nil_eq_one_of_label](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma specialMidCount_nil_eq_one_of_label_eq
  {a v du : ℂ}
  {h0 : ℤ}
  {j : Fin 3}
-- given
  (hdu : du ≠ 0)
  (ha : a = labelMid v du j) :
-- imply
  specialMidCount a h0 v du [] = 1 := by
-- proof
  apply StatMech.Universality.specialMidCount_nil_eq_one_of_label hdu j ha

/--
[hexEndpoint_support_endsAt_label_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_support_endsAt_label_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {ts : List ℤ}
-- given
  (hsupport : endpointCombinedSummand R.inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts ≠ 0) :
-- imply
  ∃ e : Fin 3, (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e) := by
-- proof
  apply StatMech.Universality.hexEndpoint_support_endsAt_label_aw R c ts hsupport

/--
[hexEndpoint_countOne_launch_of_mem_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countOne_launch_of_mem_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {base : List ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
-- imply
  ∃ e : Fin 3, HexCyclicLaunch hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e base := by
-- proof
  apply StatMech.Universality.hexEndpoint_countOne_launch_of_mem_aw R c hnotOutside base hbase

/--
[hexEndpoint_countOne_piece_subset_oneTwo_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countOne_piece_subset_oneTwo_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {base : List ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
  (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
-- imply
  hexEndpointCanonicalTripletPiece base ⊆ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 := by
-- proof
  apply StatMech.Universality.hexEndpoint_countOne_piece_subset_oneTwo_aw R c hnotOutside hall base hbase

/--
[hexEndpoint_countOne_piece_sum_zero_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countOne_piece_sum_zero_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {base : List ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
  (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) :
-- imply
  ∑ ts ∈ hexEndpointCanonicalTripletPiece base, endpointCombinedSummand R.inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
-- proof
  apply StatMech.Universality.hexEndpoint_countOne_piece_sum_zero_aw R c hnotOutside hall base hbase

/--
[hexEndpoint_mem_countOne_piece_classify_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_mem_countOne_piece_classify_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {base z : List ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hbase : base ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1)
  (hz : z ∈ hexEndpointCanonicalTripletPiece base) :
-- imply
  (z = base ∧ specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) z = 1) ∨ (z.dropLast = base ∧ specialMidCount hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) z = 2) := by
-- proof
  apply StatMech.Universality.hexEndpoint_mem_countOne_piece_classify_aw R c hnotOutside base z hbase hz

/--
[hexEndpoint_countOne_tripletPieces_disjoint_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countOne_tripletPieces_disjoint_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0) :
-- imply
  (↑(R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1) : Set (List ℤ)).PairwiseDisjoint hexEndpointCanonicalTripletPiece := by
-- proof
  apply StatMech.Universality.hexEndpoint_countOne_tripletPieces_disjoint_aw R c hnotOutside

/--
[hexEndpoint_countTwo_mem_dropLast_piece_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countTwo_mem_dropLast_piece_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
  {ts : List ℤ}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
  (hreturn : ∀ ws : List ℤ, (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧ (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = [])
  (hts : ts ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2) :
-- imply
  ts.dropLast ∈ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∧ ts ∈ hexEndpointCanonicalTripletPiece ts.dropLast := by
-- proof
  apply StatMech.Universality.hexEndpoint_countTwo_mem_dropLast_piece_aw R c hnotOutside hall hreturn ts hts

/--
[hexEndpoint_countOne_biUnion_eq_oneTwo_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_countOne_biUnion_eq_oneTwo_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
  (hreturn : ∀ ws : List ℤ, (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧ (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = []) :
-- imply
  (R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1).biUnion hexEndpointCanonicalTripletPiece = R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2 := by
-- proof
  apply StatMech.Universality.hexEndpoint_countOne_biUnion_eq_oneTwo_aw R c hnotOutside hall hreturn

/--
[hexEndpoint_visitOneTwo_sum_zero_aw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointTripletOrbit.lean)
-/
@[path]
private lemma hexEndpoint_visitOneTwo_sum_zero_aw_eq
  {R : HexFiniteRegion}
  {c : HexAWCoord}
-- given
  (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
  (hall : ∀ e : Fin 3, R.inRegion (hexAWMid c e))
  (hreturn : ∀ ws : List ℤ, (ofTurns hexAWStart 1 ws).EndpointIsLegalSAW ∧ (ofTurns hexAWStart 1 ws).StaysIn R.inRegion ∧ (ofTurns hexAWStart 1 ws).EndsAt hexAWStart → ws = []) :
-- imply
  ∑ ts ∈ (R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 1 ∪ R.endpointVisitClassFinset hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) 2), endpointCombinedSummand R.inRegion hexAWStart 1 (hexAWPos c) (hexAWMid c 0 - hexAWPos c) ts = 0 := by
-- proof
  apply StatMech.Universality.hexEndpoint_visitOneTwo_sum_zero_aw R c hnotOutside hall hreturn


-- created on 2026-10-23
