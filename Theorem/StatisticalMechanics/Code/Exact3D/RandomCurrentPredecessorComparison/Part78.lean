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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part70
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_eq_empty_add_inner
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0 m =
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m +
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m := by
  rw [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand,
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentBranchSummand_eq_empty_add_inner]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0 m := by
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand]
  exact
    mul_nonneg (by positivity)
      (doubledBoxResidualMomentBranchSummand_nonneg hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand]
  exact
    mul_nonneg (by positivity)
      (doubledBoxResidualMomentEmptyBranchSummand_nonneg
        (n := n) (v := v) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  dsimp [doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand]
  exact
    mul_nonneg (by positivity)
      (doubledBoxResidualMomentInnerPairBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_finset_sum_nonneg
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_nonneg
        hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_congr_w
    (β : ℝ) (n : ℕ) (v w w' : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w e0
        m =
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w'
        e0 m := by
  rfl

end Exact3D
end StatMech
