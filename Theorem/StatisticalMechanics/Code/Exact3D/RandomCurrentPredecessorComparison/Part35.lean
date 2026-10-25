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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part33
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0 m := by
  classical
  let Iin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementMultiplicityIndex
      (n := n) (w := w) m e0
  let Iout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementMultiplicityIndex
      (n := n) (w := w) m e0
  let Win : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m' =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m'
  let Wout : (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m' =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m'
  have hJ : ∀ e : Sym2 (FK.boxVerts 3 (2 * n)), 0 ≤ (fun _ => (1 : ℝ)) e := by
    intro e
    exact zero_le_one
  change
    0 ≤
      (∑ m' ∈ Iin.image, (((Iin.fiber m').card : ℕ) : ℝ) * Win m') +
        ∑ m' ∈ Iout.image, (((Iout.fiber m').card : ℕ) : ℝ) * Wout m'
  refine add_nonneg ?_ ?_
  · refine Finset.sum_nonneg ?_
    intro m' _hm'
    have hcard : 0 ≤ (((Iin.fiber m').card : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (Iin.fiber m').card
    have hW : 0 ≤ Win m' := by
      dsimp [Win]
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m' hβ hJ
    exact mul_nonneg hcard hW
  · refine Finset.sum_nonneg ?_
    intro m' _hm'
    have hcard : 0 ≤ (((Iout.fiber m').card : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (Iout.fiber m').card
    have hW : 0 ≤ Wout m' := by
      dsimp [Wout]
      exact
        edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m' hβ hJ
    exact mul_nonneg hcard hW

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_finset_sum_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSelectedCopyDecrementImageBranchSum_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCard_mul_sourcePairSummands
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1)) =
      (((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m) +
      (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m) := by
  classical
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  have hdec : Function.update M e0 (M e0 - 1) = m := by
    simp [M]
  rw [doubledBoxSelectedCopyDecrementImageBranchSum]
  rw [← doubledBox_selectedEdgeCopyPairsInCurrent_sourcePairSummand_sum_eq_decrementImage_sum
        (β := β) (n := n) (v := v) (w := w) M e0,
      ← doubledBox_selectedEdgeCopyPairsOutsideCurrent_sourcePairSummand_sum_eq_decrementImage_sum
        (β := β) (n := n) (v := v) (w := w) M e0]
  change
    (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) M e0,
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n)))
        (Function.update M p.2.1 (M p.2.1 - 1))) +
      (∑ p ∈ edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) M e0,
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)
        (Function.update M p.2.1 (M p.2.1 - 1))) =
    _
  congr 1
  · rw [Finset.sum_congr rfl]
    · rw [Finset.sum_const, nsmul_eq_mul]
    · intro p hp
      have hpbranch :=
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 p).mp hp
      have hbase :=
        (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 p).mp hpbranch.1
      have hpe : p.2.1 = e0 := hbase.2
      rw [hpe, hdec]
  · rw [Finset.sum_congr rfl]
    · rw [Finset.sum_const, nsmul_eq_mul]
    · intro p hp
      have hpbranch :=
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 p).mp hp
      have hbase :=
        (edgeCopySourceSectorSelectedEdgeCopyPairs_mem
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) M e0 p).mp hpbranch.1
      have hpe : p.2.1 = e0 := hbase.2
      rw [hpe, hdec]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_finset_sum_eq_branchCard_mul_sourcePairSummands
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyDecrementImageBranchSum β n v w e0
        (Function.update m e0 (m e0 + 1))) =
      ∑ m ∈ Ω,
        ((((edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1)) e0).card : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          (((edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
              (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w)
              (Function.update m e0 (m e0 + 1)) e0).card : ℕ) : ℝ) *
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyDecrementImageBranchSum_edgeIncrement_eq_branchCard_mul_sourcePairSummands
      (β := β) (n := n) (v := v) (w := w) m e0

end Exact3D
end StatMech
