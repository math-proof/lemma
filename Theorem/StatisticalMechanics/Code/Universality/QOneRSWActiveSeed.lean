/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneRectangleCylinder
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part8
import Instance.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.FK

open StatMech.RSW.Box


theorem rq1_iUnion_activeExtremalPairCandidate (n : ℤ) :
    (⋃ pair : Rq1ActiveExtremalPair n,
        rlc_extremalPairCandidate pair.1) =
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n := by
  rw [← rlc_iUnion_extremalPairCandidate n]
  ext omega
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨pair, homega⟩
    exact ⟨pair.1, homega⟩
  · rintro ⟨pair, homega⟩
    exact ⟨⟨pair, ⟨omega, homega⟩⟩, homega⟩


theorem rq1_activeExtremalPairCandidate_pairwiseDisjoint {n : ℤ}
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise (fun pair pair' : Rq1ActiveExtremalPair n =>
      Disjoint (rlc_extremalPairCandidate pair.1)
        (rlc_extremalPairCandidate pair'.1)) := by
  intro pair pair' hne
  apply rlc_extremalPairCandidate_pairwiseDisjoint hright hleft
  intro heq
  apply hne
  exact Subtype.ext heq


theorem rq1_scaleTwo_not_universal_failure_to_reflected_success :
    ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap →
        rlc_dualReflectConfig omega ∈
          rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap) := by
  intro h
  exact rlc_scaleTwoDoubleFailure_reflected_failure
    (h rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)


theorem rq1_axisGapEdges_subset_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1)) :
    rlc_axisGapEdges G ⊆ rlc_mixedAxisGapEdges G := by
  intro e he
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  constructor
  · simp only [Finset.mem_union]
    exact Or.inl (Or.inl he)
  · intro hpath
    rw [Finset.mem_union] at hpath
    rcases hpath with hright | hleft
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_axisGapEdges G hdisj)) hright he
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_axisGapEdges G hdisj)) hleft he


theorem rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdisj : Disjoint (rlc_pathVertices gamma.1)
      (rlc_pathVertices gamma'.1)) :
    rlc_axisGapConnectorEvent G ⊆ rlc_mixedAxisGapConnectorEvent G := by
  intro omega homega
  obtain ⟨x, hx, y, hy, hxR, hyR, hxy⟩ := homega
  refine ⟨x, hx, y, hy, hxR, hyR, ?_⟩
  apply StatMech.TwoDim.connectedWithin_mono _ hxy
  intro e
  by_cases he : e ∈ rlc_axisGapEdges G
  · have hemix := rq1_axisGapEdges_subset_mixedAxisGapEdges G hdisj he
    simp [rlc_maskConfig, he, hemix]
  · simp [rlc_maskConfig, he]


end Universality
end StatMech
