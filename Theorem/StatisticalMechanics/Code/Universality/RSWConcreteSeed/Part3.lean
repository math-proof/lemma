/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


theorem rcs_iUnion_pathPairOpen (n : ℤ) :
    (⋃ i : RcsPathPair n, rcs_pathPairOpen i) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  rw [← rcs_right_between_eq_diagonal n, ← rcs_left_between_eq_diagonal n,
    ← rlc_iUnion_betweenPathOpen, ← rlc_iUnion_betweenPathOpen]
  ext omega
  simp only [rcs_pathPairOpen, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨g, h⟩, hg, hh⟩
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨h, hh⟩⟩
    exact ⟨⟨g, h⟩, hg, hh⟩


theorem rcs_pathPairEdges_disjoint_mixedAdaptiveEdges {n : ℤ}
    (pair : RlcDiagonalPathPair n) :
    Disjoint (rlc_pathPairEdges pair)
      (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
  rw [Finset.disjoint_left]
  intro e hePair heFresh
  rw [rlc_pathPairEdges, Finset.mem_union] at hePair
  rcases hePair with heRight | heLeft
  · exact (Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heRight heFresh
  · exact (Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heLeft heFresh


theorem rcs_extremalPairCandidateEdges_disjoint_of_competitors {n : ℤ}
    (pair : RlcDiagonalPathPair n)
    (hcompetitors : Disjoint
      (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2)
      (rlc_mixedAdaptiveEdges pair.1 pair.2)) :
    Disjoint (rlc_extremalPairCandidateEdges pair)
      (rlc_mixedAdaptiveEdges pair.1 pair.2) := by
  rw [Finset.disjoint_left]
  intro e heCandidate heFresh
  rw [rlc_extremalPairCandidateEdges, Finset.mem_union,
    rlc_rightLowestCandidateEdges, rlc_leftHighestCandidateEdges,
    Finset.mem_union, Finset.mem_union] at heCandidate
  rcases heCandidate with (heRight | heLower) | heLeft | heUpper
  · exact (Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heRight heFresh
  · exact (Finset.disjoint_left.mp hcompetitors)
      (Finset.mem_union_left _ heLower) heFresh
  · exact (Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_mixedAdaptiveEdges pair.1 pair.2))
        heLeft heFresh
  · exact (Finset.disjoint_left.mp hcompetitors)
      (Finset.mem_union_right _ heUpper) heFresh


theorem rcs_four_by_two_crossing_lower_bound (n : ℤ) (hn : 0 < n)
    (hanchor : RlcRightCanonicalAnchorReachability n)
    (hcompetitors : ∀ pair : RlcDiagonalPathPair n,
      Disjoint
        (rlc_rightLowerPathEdges pair.1 ∪ rlc_leftUpperPathEdges pair.2)
        (rlc_mixedAdaptiveEdges pair.1 pair.2))
    (hconnector : ∀ pair : RlcDiagonalPathPair n,
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real
        (rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)) :
    (1 : ℝ) / 2048 ≤ rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n) := by
  let Sright := edgesWithinFinset
    (rect_finite 0 (2 * n) (-n) n).toFinset
  let Sleft := edgesWithinFinset
    (rect_finite (-2 * n) 0 (-n) n).toFinset
  have hsafe : RlcRightSafeTraceReachability n :=
    rlc_rightSafeTraceReachability_of_canonicalAnchor hn hanchor
  obtain ⟨hright, hleft⟩ :=
    rlc_envelopeProperties_of_rightSafeTraceReachability hsafe
  have hseed := rlc_bernoulli_rsw_stopping_sixth_power
    (E := Sym2 (Site 2)) (p := (2⁻¹ : NNReal)) half_le_one
    ((1 : ℝ) / 2) (by norm_num)
    (rlc_rightDiagonal n) (rlc_leftDiagonal n)
    (horizontalCrossingEvent (-2 * n) (2 * n) (-n) n)
    Sright Sleft
    (rlc_lrRestrictedEvent_isIncreasing 0 (2 * n) (-n) n
      rlc_lowerHalf rlc_upperHalf)
    (rlc_lrRestrictedEvent_isIncreasing (-2 * n) 0 (-n) n
      rlc_lowerHalf rlc_upperHalf)
    (by
      simpa [Sright, rlc_rightDiagonal] using
        rlc_lrRestrictedEvent_dependsOn 0 (2 * n) (-n) n
          rlc_lowerHalf rlc_upperHalf)
    (by
      simpa [Sleft, rlc_leftDiagonal] using
        rlc_lrRestrictedEvent_dependsOn (-2 * n) 0 (-n) n
          rlc_lowerHalf rlc_upperHalf)
    (by
      convert rlc_half_rightDiagonal_unconditional n hn using 1
      all_goals norm_num [rba_selfDualMeasure])
    (by
      convert rlc_half_leftDiagonal_unconditional n hn using 1
      all_goals norm_num [rba_selfDualMeasure])
    (fun pair : RlcDiagonalPathPair n => rlc_extremalPairCandidate pair)
    (fun pair : RlcDiagonalPathPair n =>
      rlc_mixedAdaptiveConnectorEvent pair.1 pair.2)
    (fun pair : RlcDiagonalPathPair n => rlc_extremalPairCandidateEdges pair)
    (fun pair : RlcDiagonalPathPair n => rlc_mixedAdaptiveEdges pair.1 pair.2)
    (rlc_iUnion_extremalPairCandidate n)
    (rlc_extremalPairCandidate_pairwiseDisjoint hright hleft)
    rlc_extremalPairCandidate_dependsOn
    (fun pair => rlc_mixedAdaptiveConnectorEvent_dependsOn pair.1 pair.2)
    (fun pair =>
      rcs_extremalPairCandidateEdges_disjoint_of_competitors pair
        (hcompetitors pair))
    hconnector
    (fun pair omega homega =>
      rlc_mixedAdaptiveConnector_glues_horizontal n hn pair.1 pair.2
        ⟨rlc_extremalPairCandidate_subset_pathPairOpen pair homega.1,
          homega.2⟩)
  norm_num [rba_selfDualMeasure] at hseed ⊢
  exact hseed

end Universality
end StatMech
