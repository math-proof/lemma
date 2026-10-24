import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed
open Set SimpleGraph MeasureTheory StatMech StatMech.Universality


/--
[rq1_iUnion_activeExtremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_iUnion_activeExtremalPairCandidate_eq
  {n : ℤ} :
-- imply
  (⋃ pair : Rq1ActiveExtremalPair n, rlc_extremalPairCandidate pair.1) = rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rq1_iUnion_activeExtremalPairCandidate n

/--
[rq1_activeExtremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_activeExtremalPairCandidate_pairwiseDisjoint_eq
  {n : ℤ}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise (fun pair pair' : Rq1ActiveExtremalPair n => Disjoint (rlc_extremalPairCandidate pair.1) (rlc_extremalPairCandidate pair'.1)) := by
-- proof
  apply StatMech.Universality.rq1_activeExtremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rq1_scaleTwo_not_universal_failure_to_reflected_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_scaleTwo_not_universal_failure_to_reflected_success_eq :
-- imply
  ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap → rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap) := by
-- proof
  apply StatMech.Universality.rq1_scaleTwo_not_universal_failure_to_reflected_success

/--
[rq1_axisGapEdges_subset_mixedAxisGapEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_axisGapEdges_subset_mixedAxisGapEdges_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  rlc_axisGapEdges G ⊆ rlc_mixedAxisGapEdges G := by
-- proof
  apply StatMech.Universality.rq1_axisGapEdges_subset_mixedAxisGapEdges G hdisj

/--
[rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hdisj : Disjoint (rlc_pathVertices gamma.1) (rlc_pathVertices gamma'.1)) :
-- imply
  rlc_axisGapConnectorEvent G ⊆ rlc_mixedAxisGapConnectorEvent G := by
-- proof
  apply StatMech.Universality.rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent G hdisj

/--
[rq1_adaptiveWiredConnectorEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_adaptiveWiredConnectorEvent_dependsOn_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  _root_.DependsOn ((rq1_adaptiveWiredConnectorEvent gamma gamma').indicator (fun _ => (1 : ℝ))) (rlc_mixedAdaptiveEdges gamma gamma' : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Universality.rq1_adaptiveWiredConnectorEvent_dependsOn gamma gamma'

/--
[rq1_adaptiveWiredConnector_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_adaptiveWiredConnector_glues_horizontal_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩ rq1_adaptiveWiredConnectorEvent gamma gamma' ⊆ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rq1_adaptiveWiredConnector_glues_horizontal hn gamma gamma'

/--
[rq1_adaptiveWiredConnector_half_of_retainedTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_adaptiveWiredConnector_half_of_retainedTopology_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n)
  (htopology : ∀ (G : RlcAxisBarrierGap gamma gamma'), rlc_axisBarrierGap? gamma gamma' = some G → G.lower + 1 < G.upper → RlcFailureSelectedExtremalTraceTopology G) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rq1_adaptiveWiredConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rq1_adaptiveWiredConnector_half_of_retainedTopology gamma gamma' hn htopology

/--
[rq1_active_four_by_two_crossing_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_active_four_by_two_crossing_lower_bound_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hanchor : RlcRightCanonicalAnchorReachability n)
  (hcompetitors : ∀ pair : RlcDiagonalPathPair n, (rlc_extremalPairCandidate pair).Nonempty → Disjoint (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2) (rlc_mixedAdaptiveEdges pair.1 pair.2))
  (hconnector : ∀ pair : RlcDiagonalPathPair n, (rlc_extremalPairCandidate pair).Nonempty → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
-- imply
  (1 : ℝ) / 2048 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rq1_active_four_by_two_crossing_lower_bound n hn hanchor hcompetitors hconnector

/--
[rq1_wiredInfiniteVolume_active_four_by_two_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean)
-/
@[path]
private lemma rq1_wiredInfiniteVolume_active_four_by_two_lower_bound_eq
  {N : ℕ}
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hrect : rect (-2 * n) (2 * n) (-n) n ⊆ box 2 N)
  (hanchor : RlcRightCanonicalAnchorReachability n)
  (hcompetitors : ∀ pair : RlcDiagonalPathPair n, (rlc_extremalPairCandidate pair).Nonempty → Disjoint (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2) (rlc_mixedAdaptiveEdges pair.1 pair.2))
  (hconnector : ∀ pair : RlcDiagonalPathPair n, (rlc_extremalPairCandidate pair).Nonempty → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
-- imply
  (1 : ℝ) / 2048 ≤ (wiredInfiniteVolume 2 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) (by norm_num : (0 : ℝ) < 1) : Measure (ConfigSpace (Sym2 (Site 2)))).real (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rq1_wiredInfiniteVolume_active_four_by_two_lower_bound N n hn hrect hanchor hcompetitors hconnector


-- created on 2026-10-23
