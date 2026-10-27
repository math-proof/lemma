import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[RlcSourceRightFullCrossing.axis_contact_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma axis_contact_eq_endpoint_eq
  {n : Int}
  {gamma : RlcSourceRightFullCrossing n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1.1)
  (hz0 : z 0 = 0) :
-- imply
  z = (gamma.1.1.1 : Site 2) := by
-- proof
  apply StatMech.Universality.RlcSourceRightFullCrossing.axis_contact_eq_endpoint gamma hz hz0

/--
[RlcSourceRightFullCrossing.axis_contact_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma axis_contact_strict_eq
  {n : Int}
  {gamma : RlcSourceRightFullCrossing n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1.1)
  (hz0 : z 0 = 0) :
-- imply
  z 1 < 0 := by
-- proof
  apply StatMech.Universality.RlcSourceRightFullCrossing.axis_contact_strict gamma hz hz0

/--
[RlcSourceLeftFullCrossing.axis_contact_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma axis_contact_eq_endpoint_eq_2
  {n : Int}
  {gamma : RlcSourceLeftFullCrossing n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1.1)
  (hz0 : z 0 = 0) :
-- imply
  z = (gamma.1.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.RlcSourceLeftFullCrossing.axis_contact_eq_endpoint gamma hz hz0

/--
[RlcSourceLeftFullCrossing.axis_contact_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma axis_contact_strict_eq_2
  {n : Int}
  {gamma : RlcSourceLeftFullCrossing n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_pathVertices gamma.1.1)
  (hz0 : z 0 = 0) :
-- imply
  0 < z 1 := by
-- proof
  apply StatMech.Universality.RlcSourceLeftFullCrossing.axis_contact_strict gamma hz hz0

/--
[rlc_sourceExtremalPairCandidate_subset_diagonalEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_sourceExtremalPairCandidate_subset_diagonalEvent_eq
  {n : Int}
  {pair : RlcSourceFullCrossingPair n} :
-- imply
  rlc_sourceExtremalPairCandidate pair ⊆ rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_sourceExtremalPairCandidate_subset_diagonalEvent pair

/--
[rlc_sourceStoppedDiagonalEvent_subset_diagonalEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_sourceStoppedDiagonalEvent_subset_diagonalEvent_eq
  {n : Int} :
-- imply
  rlc_sourceStoppedDiagonalEvent n ⊆ rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rlc_sourceStoppedDiagonalEvent_subset_diagonalEvent n

/--
[rlc_sourceExtremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_sourceExtremalPairCandidate_pairwiseDisjoint_eq
  {n : Int}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise (fun pair pair' : RlcSourceFullCrossingPair n => Disjoint (rlc_sourceExtremalPairCandidate pair) (rlc_sourceExtremalPairCandidate pair')) := by
-- proof
  apply StatMech.Universality.rlc_sourceExtremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rlc_rightWalk_first_axis_contact_from_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_rightWalk_first_axis_contact_from_outer_eq
  {n : Int}
  {x y : rect 0 (2 * n) (-n) n}
  {p : ((hypercubicLattice 2).induce (rect 0 (2 * n) (-n) n)).Walk x y}
-- given
  (hx : 0 < (x : Site 2) 0)
  (hy : (y : Site 2) 0 = 0) :
-- imply
  ∃ j ≤ p.length, (p.getVert j : Site 2) 0 = 0 ∧ ∀ m < j, 0 < (p.getVert m : Site 2) 0 := by
-- proof
  apply StatMech.Universality.rlc_rightWalk_first_axis_contact_from_outer p hx hy

/--
[rlc_leftWalk_first_axis_contact_from_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_leftWalk_first_axis_contact_from_outer_eq
  {n : Int}
  {x y : rect (-2 * n) 0 (-n) n}
  {p : ((hypercubicLattice 2).induce (rect (-2 * n) 0 (-n) n)).Walk x y}
-- given
  (hx : (x : Site 2) 0 < 0)
  (hy : (y : Site 2) 0 = 0) :
-- imply
  ∃ j ≤ p.length, (p.getVert j : Site 2) 0 = 0 ∧ ∀ m < j, (p.getVert m : Site 2) 0 < 0 := by
-- proof
  apply StatMech.Universality.rlc_leftWalk_first_axis_contact_from_outer p hx hy

/--
[rlc_exists_rightBookFaithfulSubpath_of_axis_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_exists_rightBookFaithfulSubpath_of_axis_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
-- given
  (hn : 0 < n)
  (hneg : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> z 1 < 0) :
-- imply
  ∃ delta : RlcRightDiagonalPath n, rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧ rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧ (∀ {z : Site 2}, z ∈ rlc_pathVertices delta.1 -> z 0 = 0 -> z = (delta.1.1 : Site 2)) ∧ (delta.1.1 : Site 2) 1 < 0 := by
-- proof
  apply StatMech.Universality.rlc_exists_rightBookFaithfulSubpath_of_axis_strict hn gamma hneg

/--
[rlc_exists_leftBookFaithfulSubpath_of_axis_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_exists_leftBookFaithfulSubpath_of_axis_strict_eq
  {n : Int}
  {gamma : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n)
  (hpos : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> 0 < z 1) :
-- imply
  ∃ delta : RlcLeftDiagonalPath n, rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧ rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧ (∀ {z : Site 2}, z ∈ rlc_pathVertices delta.1 -> z 0 = 0 -> z = (delta.1.2.1 : Site 2)) ∧ 0 < (delta.1.2.1 : Site 2) 1 := by
-- proof
  apply StatMech.Universality.rlc_exists_leftBookFaithfulSubpath_of_axis_strict hn gamma hpos

/--
[rlc_exists_bookFaithfulSubpaths_of_axis_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_exists_bookFaithfulSubpaths_of_axis_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n)
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1))
  (hright : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 → z 0 = 0 → z 1 < 0)
  (hleft : ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma'.1 → z 0 = 0 → 0 < z 1) :
-- imply
  ∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulTracePair delta delta' ∧ rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1 ∧ rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1 ∧ rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1 ∧ rlc_pathVertices delta'.1 ⊆ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_exists_bookFaithfulSubpaths_of_axis_strict hn gamma gamma' hdisj hright hleft

/--
[rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_finiteConnectorEvent gamma gamma' = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_finiteConnectorEvent_eq_univ_of_common_trace_vertex gamma gamma' hzRight hzLeft

/--
[rlc_extremalPairCandidate_faithfulReplacement_or_axisDefect_or_intersects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_extremalPairCandidate_faithfulReplacement_or_axisDefect_or_intersects_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n)
  (hactive : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
-- imply
  (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulStratumReplacement gamma gamma' delta delta') ∨ (∃ z ∈ rlc_pathVertices gamma.1, z 0 = 0 ∧ 0 ≤ z 1) ∨ (∃ z ∈ rlc_pathVertices gamma'.1, z 0 = 0 ∧ z 1 ≤ 0) ∨ ∃ z, z ∈ rlc_pathVertices gamma.1 ∧ z ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidate_faithfulReplacement_or_axisDefect_or_intersects hn gamma gamma' hactive

/--
[rlc_sourceExtremalPairCandidate_faithfulReplacement_or_intersects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_sourceExtremalPairCandidate_faithfulReplacement_or_intersects_eq
  {n : Int}
  {pair : RlcSourceFullCrossingPair n}
-- given
  (hn : 0 < n)
  (hactive : (rlc_sourceExtremalPairCandidate pair).Nonempty) :
-- imply
  (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulStratumReplacement pair.1.1 pair.2.1 delta delta') ∨ ∃ z, z ∈ rlc_pathVertices pair.1.1.1 ∧ z ∈ rlc_pathVertices pair.2.1.1 := by
-- proof
  apply StatMech.Universality.rlc_sourceExtremalPairCandidate_faithfulReplacement_or_intersects hn pair hactive

/--
[rlc_sourceExtremalPairCandidate_replacement_or_connectorEvent_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean)
-/
@[path]
private lemma rlc_sourceExtremalPairCandidate_replacement_or_connectorEvent_eq_univ_eq
  {n : Int}
  {pair : RlcSourceFullCrossingPair n}
-- given
  (hn : 0 < n)
  (hactive : (rlc_sourceExtremalPairCandidate pair).Nonempty) :
-- imply
  (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulStratumReplacement pair.1.1 pair.2.1 delta delta') ∨ rlc_finiteConnectorEvent pair.1.1 pair.2.1 = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_sourceExtremalPairCandidate_replacement_or_connectorEvent_eq_univ hn pair hactive


-- created on 2026-10-23
