import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part3
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rcs_centeredSquare_vertical_eq_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_centeredSquare_vertical_eq_horizontal_eq
  {n : ℤ} :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rcs_centeredSquare_vertical_eq_horizontal n

/--
[rcs_diagonal_pair_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_diagonal_pair_lower_bound_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  let alpha := rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) ∧ alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
-- proof
  apply StatMech.Universality.rcs_diagonal_pair_lower_bound n hn

/--
[rcs_right_between_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_right_between_eq_diagonal_eq
  {n : ℤ} :
-- imply
  rlc_betweenEvent (rcs_rightLower n) (rcs_rightUpper n) = rlc_rightDiagonal n := by
-- proof
  apply StatMech.Universality.rcs_right_between_eq_diagonal n

/--
[rcs_left_between_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_left_between_eq_diagonal_eq
  {n : ℤ} :
-- imply
  rlc_betweenEvent (rcs_leftLower n) (rcs_leftUpper n) = rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rcs_left_between_eq_diagonal n

/--
[rcs_iUnion_pathPairOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_iUnion_pathPairOpen_eq
  {n : ℤ} :
-- imply
  (⋃ i : RcsPathPair n, rcs_pathPairOpen i) = rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
-- proof
  apply StatMech.Universality.rcs_iUnion_pathPairOpen n

/--
[rcs_pathPairEdges_disjoint_mixedAdaptiveEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_pathPairEdges_disjoint_mixedAdaptiveEdges_eq
  {n : ℤ}
  {pair : RlcDiagonalPathPair n} :
-- imply
  Disjoint (rlc_pathPairEdges pair) (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
-- proof
  apply StatMech.Universality.rcs_pathPairEdges_disjoint_mixedAdaptiveEdges pair

/--
[rcs_extremalPairCandidateEdges_disjoint_of_competitors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_extremalPairCandidateEdges_disjoint_of_competitors_eq
  {n : ℤ}
  {pair : RlcDiagonalPathPair n}
-- given
  (hcompetitors : Disjoint (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2) (rlc_mixedAdaptiveEdges pair.1 pair.2)) :
-- imply
  Disjoint (rlc_extremalPairCandidateEdges pair) (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
-- proof
  apply StatMech.Universality.rcs_extremalPairCandidateEdges_disjoint_of_competitors pair hcompetitors

/--
[rcs_four_by_two_crossing_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean)
-/
@[path]
private lemma rcs_four_by_two_crossing_lower_bound_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hanchor : RlcRightCanonicalAnchorReachability n)
  (hcompetitors : ∀ pair : RlcDiagonalPathPair n, Disjoint (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2) (rlc_mixedAdaptiveEdges pair.1 pair.2))
  (hconnector : ∀ pair : RlcDiagonalPathPair n, (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
-- imply
  (1 : ℝ) / 2048 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
-- proof
  apply StatMech.Universality.rcs_four_by_two_crossing_lower_bound n hn hanchor hcompetitors hconnector


-- created on 2026-10-23
