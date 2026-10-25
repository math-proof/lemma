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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part28
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_residualMomentBranchSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
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
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
      ∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  calc
    (∑ m' ∈ Ω.image (fun m => Function.update m e0 (m e0 + 1)),
      ((m' e0 : ℕ) : ℝ) *
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m') ≤
        β *
          ∑ m ∈ Ω,
            (((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
              ((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w) m) :=
      doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_beta_mul_preimage_edgeMultiplicitySucc_branchSourcePairSummand_sum
        (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw
    _ = ∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      rw [Finset.mul_sum]
      rfl

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_residualMomentBranchSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hβ : 0 ≤ β)
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
    β * (∑ m ∈ Ω,
        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
      ∑ m ∈ Ω, doubledBoxResidualMomentBranchSummand β n v w e0 m :=
  (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul
    (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw).trans
    (doubledBox_edgeIncrement_image_count_mul_targetTerm_finset_sum_le_residualMomentBranchSummand_sum
      (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw)

set_option linter.style.longLine false in


theorem doubledBoxResidualMomentBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  dsimp [doubledBoxResidualMomentBranchSummand]
  refine mul_nonneg hβ (add_nonneg ?_ ?_)
  · exact
      mul_nonneg (by positivity)
        (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
          (by intro e; norm_num))
  · exact
      mul_nonneg (by positivity)
        (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m hβ
          (by intro e; norm_num))

end Exact3D
end StatMech
