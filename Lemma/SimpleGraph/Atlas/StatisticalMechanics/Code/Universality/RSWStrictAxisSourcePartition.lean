import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
open Finset SimpleGraph Set MeasureTheory StatMech StatMech.Universality


/--
[RlcStrictAxisRightFullCrossing.axis_nonnegative_mem_strictTopSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma axis_nonnegative_mem_strictTopSet_eq
  {n : Int}
  {gamma : RlcStrictAxisRightFullCrossing n}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hzR : z ∈ rect 0 (2 * n) (-n) n)
  (hz0 : z 0 = 0)
  (hz1 : 0 ≤ z 1) :
-- imply
  z ∈ rlc_strictTopSet gamma.1 := by
-- proof
  apply StatMech.Universality.RlcStrictAxisRightFullCrossing.axis_nonnegative_mem_strictTopSet hn gamma hzR hz0 hz1

/--
[RlcStrictAxisLeftFullCrossing.axis_nonpositive_mem_strictBottomSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma axis_nonpositive_mem_strictBottomSet_eq
  {n : Int}
  {gamma : RlcStrictAxisLeftFullCrossing n}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hzR : z ∈ rect (-2 * n) 0 (-n) n)
  (hz0 : z 0 = 0)
  (hz1 : z 1 ≤ 0) :
-- imply
  z ∈ rlc_strictBottomSet gamma.1 := by
-- proof
  apply StatMech.Universality.RlcStrictAxisLeftFullCrossing.axis_nonpositive_mem_strictBottomSet hn gamma hzR hz0 hz1

/--
[rlc_rightLowestCandidate_explored_subset_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_explored_subset_of_open_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (henv : RlcRightEnvelopeProperty n)
  (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1) :
-- imply
  rlc_rightExploredVertices gamma ⊆ rlc_rightExploredVertices delta := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_explored_subset_of_open henv hgamma hdelta

/--
[rlc_leftHighestCandidate_explored_subset_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_explored_subset_of_open_eq
  {n : Int}
  {gamma delta : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (henv : RlcLeftEnvelopeProperty n)
  (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1) :
-- imply
  rlc_leftExploredVertices gamma ⊆ rlc_leftExploredVertices delta := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_explored_subset_of_open henv hgamma hdelta

/--
[rlc_rightLowestCandidate_axis_strict_of_open_strictAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_axis_strict_of_open_strictAxis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {delta : RlcStrictAxisRightFullCrossing n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (henv : RlcRightEnvelopeProperty n)
  (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1.1) :
-- imply
  ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> z 1 < 0 := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_axis_strict_of_open_strictAxis hn henv delta hgamma hdelta

/--
[rlc_leftHighestCandidate_axis_strict_of_open_strictAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_axis_strict_of_open_strictAxis_eq
  {n : Int}
  {gamma : RlcLeftDiagonalPath n}
  {delta : RlcStrictAxisLeftFullCrossing n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (henv : RlcLeftEnvelopeProperty n)
  (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1.1) :
-- imply
  ∀ {z : Site 2}, z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 -> 0 < z 1 := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_axis_strict_of_open_strictAxis hn henv delta hgamma hdelta

/--
[rlc_iUnion_strictAxisExtremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_iUnion_strictAxisExtremalPairCandidate_eq
  {n : Int}
-- given
  (hn : 0 < n)
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  rlc_strictAxisStoppedDiagonalEvent n = rlc_strictAxisRightSourceEvent n ∩ rlc_strictAxisLeftSourceEvent n := by
-- proof
  apply StatMech.Universality.rlc_iUnion_strictAxisExtremalPairCandidate hn hright hleft

/--
[rlc_strictAxisExtremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisExtremalPairCandidate_pairwiseDisjoint_eq
  {n : Int}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise (fun pair pair' : RlcStrictAxisFullCrossingPair n => Disjoint (rlc_strictAxisExtremalPairCandidate pair) (rlc_strictAxisExtremalPairCandidate pair')) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisExtremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rlc_strictAxisRightSourceEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisRightSourceEvent_isIncreasing_eq
  {n : Int} :
-- imply
  IsIncreasing (rlc_strictAxisRightSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisRightSourceEvent_isIncreasing n

/--
[rlc_strictAxisLeftSourceEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisLeftSourceEvent_isIncreasing_eq
  {n : Int} :
-- imply
  IsIncreasing (rlc_strictAxisLeftSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisLeftSourceEvent_isIncreasing n

/--
[rlc_pathEdges_subset_edgesWithinFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_pathEdges_subset_edgesWithinFinset_eq
  {a b c d : Int}
  {gamma : RlcCrossingPath a b c d} :
-- imply
  rlc_pathEdges gamma ⊆ edgesWithinFinset (rect_finite a b c d).toFinset := by
-- proof
  apply StatMech.Universality.rlc_pathEdges_subset_edgesWithinFinset gamma

/--
[rlc_strictAxisRightSourceEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisRightSourceEvent_dependsOn_eq
  {n : Int} :
-- imply
  _root_.DependsOn ((rlc_strictAxisRightSourceEvent n).indicator (fun _ => (1 : Real))) (edgesWithinFinset (rect_finite 0 (2 * n) (-n) n).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisRightSourceEvent_dependsOn n

/--
[rlc_strictAxisLeftSourceEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisLeftSourceEvent_dependsOn_eq
  {n : Int} :
-- imply
  _root_.DependsOn ((rlc_strictAxisLeftSourceEvent n).indicator (fun _ => (1 : Real))) (edgesWithinFinset (rect_finite (-2 * n) 0 (-n) n).toFinset : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisLeftSourceEvent_dependsOn n

/--
[rlc_strictAxisStoppedDiagonalEvent_mass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisStoppedDiagonalEvent_mass_lower_eq
  {p : NNReal}
  {n : Int}
  {a b : Real}
-- given
  (hp : p ≤ 1)
  (hn : 0 < n)
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n)
  (hb0 : 0 ≤ b)
  (ha : a ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_strictAxisRightSourceEvent n))
  (hb : b ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_strictAxisLeftSourceEvent n)) :
-- imply
  a * b ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_strictAxisStoppedDiagonalEvent n) := by
-- proof
  apply StatMech.Universality.rlc_strictAxisStoppedDiagonalEvent_mass_lower p hp hn hright hleft hb0 ha hb

/--
[rlc_strictAxisExtremalPairCandidate_faithfulReplacement_or_intersects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisExtremalPairCandidate_faithfulReplacement_or_intersects_eq
  {n : Int}
  {pair : RlcStrictAxisFullCrossingPair n}
-- given
  (hn : 0 < n)
  (hactive : (rlc_strictAxisExtremalPairCandidate pair).Nonempty) :
-- imply
  (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulStratumReplacement pair.1.1 pair.2.1 delta delta') ∨ ∃ z, z ∈ rlc_pathVertices pair.1.1.1 ∧ z ∈ rlc_pathVertices pair.2.1.1 := by
-- proof
  apply StatMech.Universality.rlc_strictAxisExtremalPairCandidate_faithfulReplacement_or_intersects hn pair hactive

/--
[rlc_strictAxisExtremalPairCandidate_replacement_or_connectorEvent_eq_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean)
-/
@[path]
private lemma rlc_strictAxisExtremalPairCandidate_replacement_or_connectorEvent_eq_univ_eq
  {n : Int}
  {pair : RlcStrictAxisFullCrossingPair n}
-- given
  (hn : 0 < n)
  (hactive : (rlc_strictAxisExtremalPairCandidate pair).Nonempty) :
-- imply
  (∃ (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n), RlcBookFaithfulStratumReplacement pair.1.1 pair.2.1 delta delta') ∨ rlc_finiteConnectorEvent pair.1.1 pair.2.1 = Set.univ := by
-- proof
  apply StatMech.Universality.rlc_strictAxisExtremalPairCandidate_replacement_or_connectorEvent_eq_univ hn pair hactive


-- created on 2026-10-23
