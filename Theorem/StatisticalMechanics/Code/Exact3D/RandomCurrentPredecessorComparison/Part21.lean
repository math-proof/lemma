/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part20
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsInCurrent_sourcePairSummand_sum_eq_decrementImage_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update m p.2.1 (m p.2.1 - 1))) =
      ∑ m' ∈ (doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
          (n := n) (w := w) m e0).image,
        (((doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
          (n := n) (w := w) m e0).fiber m').card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m' := by
  classical
  let I :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
      (n := n) (w := w) m e0
  let W : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m' =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m'
  change
    Finset.sum (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
      (fun p => W (Function.update m p.2.1 (m p.2.1 - 1))) =
      ∑ m' ∈ I.image, (((I.fiber m').card : ℝ) * W m')
  rw [← Finset.sum_attach]
  change
    Finset.sum I.domain (fun a => W (I.map a)) =
      ∑ m' ∈ I.image, (((I.fiber m').card : ℝ) * W m')
  exact FinsetFiberIndex.sum_fiber_weight I W

set_option linter.style.longLine false in


theorem doubledBox_selectedEdgeCopyPairsOutsideCurrent_sourcePairSummand_sum_eq_decrementImage_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0,
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update m p.2.1 (m p.2.1 - 1))) =
      ∑ m' ∈ (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
          (n := n) (w := w) m e0).image,
        (((doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
          (n := n) (w := w) m e0).fiber m').card : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m' := by
  classical
  let I :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
      (n := n) (w := w) m e0
  let W : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m' =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m'
  change
    Finset.sum (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m e0)
      (fun p => W (Function.update m p.2.1 (m p.2.1 - 1))) =
      ∑ m' ∈ I.image, (((I.fiber m').card : ℝ) * W m')
  rw [← Finset.sum_attach]
  change
    Finset.sum I.domain (fun a => W (I.map a)) =
      ∑ m' ∈ I.image, (((I.fiber m').card : ℝ) * W m')
  exact FinsetFiberIndex.sum_fiber_weight I W

set_option linter.style.longLine false in


theorem doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedEdgeCopyBranchSourcePairSummandImageSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ((m e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m ≤
      β *
        ((∑ m' ∈ (doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
            (n := n) (w := w) m e0).image,
          (((doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
            (n := n) (w := w) m e0).fiber m').card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) m') +
          ∑ m' ∈ (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
            (n := n) (w := w) m e0).image,
          (((doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
            (n := n) (w := w) m e0).fiber m').card : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m') := by
  have h :=
    doubledBox_edge_count_mul_targetTerm_le_beta_mul_selectedEdgeCopyBranchSourcePairSummandSums
      (n := n) (v := v) (w := w) hβ m e0 hedge hov how hvw
  rw [doubledBox_selectedEdgeCopyPairsInCurrent_sourcePairSummand_sum_eq_decrementImage_sum
      (β := β) (n := n) (v := v) (w := w) m e0,
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_sourcePairSummand_sum_eq_decrementImage_sum
      (β := β) (n := n) (v := v) (w := w) m e0] at h
  exact h


end Exact3D
end StatMech
