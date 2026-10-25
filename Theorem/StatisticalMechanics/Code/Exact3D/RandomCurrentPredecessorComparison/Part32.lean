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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part30
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchBounds_of_sourcePairBounds
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (h :
      doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0) :
    doubledBoxSameBetaResidualBranchBounds β n v w e0 := by
  rcases h with ⟨hempty, hinner⟩
  constructor
  · simpa [doubledBoxSameBetaResidualBranchSourcePairBounds,
      doubledBoxSameBetaResidualBranchBounds,
      doubledBoxSameBetaResidualEmptyBranchSourcePairBound,
      doubledBoxSameBetaResidualEmptyBranchBound,
      sourcePairSum_eq_edgeCopySourcePairSum] using hempty
  · simpa [doubledBoxSameBetaResidualBranchSourcePairBounds,
      doubledBoxSameBetaResidualBranchBounds,
      doubledBoxSameBetaResidualInnerPairBranchSourcePairBound,
      doubledBoxSameBetaResidualInnerPairBranchBound,
      sourcePairSum_eq_edgeCopySourcePairSum] using hinner

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (h :
      doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0) :
    doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  simpa [doubledBoxSameBetaResidualEmptyBranchSourcePairBound,
    doubledBoxSameBetaResidualEmptyBranchBound,
    sourcePairSum_eq_edgeCopySourcePairSum] using h

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (h :
      doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0) :
    doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  simpa [doubledBoxSameBetaResidualInnerPairBranchSourcePairBound,
    doubledBoxSameBetaResidualInnerPairBranchBound,
    sourcePairSum_eq_edgeCopySourcePairSum] using h

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_of_support_zero
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsupport :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        m e0 ≠ 0 →
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0) :
    doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  have hshift :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_eq_same_beta_of_support_zero
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) e0 hsupport
  dsimp [doubledBoxSameBetaResidualEmptyBranchBound,
    doubledBoxResidualMomentEmptyBranchSummand]
  rw [tsum_mul_left, hshift]

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_of_support_zero
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsupport :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        m e0 ≠ 0 →
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0) :
    doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  simpa [doubledBoxSameBetaResidualEmptyBranchSourcePairBound,
    doubledBoxSameBetaResidualEmptyBranchBound,
    sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSameBetaResidualEmptyBranchBound_of_support_zero
      β n v e0 hsupport

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_of_support_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsupport :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        m e0 ≠ 0 →
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m = 0) :
    doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  have hshift :=
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_eq_same_beta_of_support_zero
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) e0 hsupport
  dsimp [doubledBoxSameBetaResidualInnerPairBranchBound,
    doubledBoxResidualMomentInnerPairBranchSummand]
  rw [tsum_mul_left, hshift]

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_of_support_zero
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hsupport :
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        m e0 ≠ 0 →
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m = 0) :
    doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  simpa [doubledBoxSameBetaResidualInnerPairBranchSourcePairBound,
    doubledBoxSameBetaResidualInnerPairBranchBound,
    sourcePairSum_eq_edgeCopySourcePairSum] using
    doubledBoxSameBetaResidualInnerPairBranchBound_of_support_zero
      β n v w e0 hsupport

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_forces_edgeMultiplicity_tsum_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualEmptyBranchBound β n v e0) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) = 0 := by
  have hraw :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        β * (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
        β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [doubledBoxSameBetaResidualEmptyBranchBound,
      doubledBoxResidualMomentEmptyBranchSummand] using hbound
  rw [tsum_mul_left] at hraw
  have hle :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    le_of_mul_le_mul_left hraw hβpos
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_eq_zero
      (FK.boxGraph 3 (2 * n)) (le_of_lt hβpos) (fun _ => 1)
      (by intro e; norm_num) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) e0 hle

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_forces_edgeMultiplicity_tsum_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) = 0 :=
  doubledBoxSameBetaResidualEmptyBranchBound_forces_edgeMultiplicity_tsum_eq_zero
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_forces_sourcePairSummand_eq_zero_of_pos
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 := by
  have hzero :=
    doubledBoxSameBetaResidualEmptyBranchBound_forces_edgeMultiplicity_tsum_eq_zero
      hβpos n v e0 hbound
  exact
    edgeMultiplicity_tsum_eq_zero_forces_sourcePairSummand_eq_zero_of_pos
      (FK.boxGraph 3 (2 * n)) (le_of_lt hβpos) (fun _ => 1)
      (by intro e; norm_num) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) e0 hzero m hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_forces_sourcePairSummand_eq_zero_of_pos
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
  doubledBoxSameBetaResidualEmptyBranchBound_forces_sourcePairSummand_eq_zero_of_pos
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
    m hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hsummand_ne :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≠ 0) :
    m e0 = 0 := by
  by_contra hmne
  have hmpos : 0 < m e0 := Nat.pos_of_ne_zero hmne
  have hzero :=
    doubledBoxSameBetaResidualEmptyBranchBound_forces_sourcePairSummand_eq_zero_of_pos
      hβpos n v e0 hbound m hmpos
  exact hsummand_ne hzero

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualEmptyBranchBound β n v e0 ↔
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≠ 0 →
          m e0 = 0 := by
  constructor
  · intro hbound m hsummand_ne
    exact
      doubledBoxSameBetaResidualEmptyBranchBound_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
        hβpos n v e0 hbound m hsummand_ne
  · intro hsupport
    exact
      doubledBoxSameBetaResidualEmptyBranchBound_of_support_zero β n v e0
        (fun m hmne => by
          by_contra hsummand_ne
          exact hmne (hsupport m hsummand_ne))

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 ↔
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≠ 0 →
          m e0 = 0 := by
  constructor
  · intro hbound
    exact
      (doubledBoxSameBetaResidualEmptyBranchBound_iff_support_zero
        hβpos n v e0).1
        (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
  · intro hsupport
    exact
      doubledBoxSameBetaResidualEmptyBranchSourcePairBound_of_support_zero
        β n v e0
        (fun m hmne => by
          by_contra hsummand_ne
          exact hmne (hsupport m hsummand_ne))

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_pos_sourcePairSummand
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0)
    (hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  intro hbound
  have hzero :=
    doubledBoxSameBetaResidualEmptyBranchBound_forces_sourcePairSummand_eq_zero_of_pos
      hβpos n v e0 hbound m hmpos
  exact (ne_of_gt hsummand_pos) hzero

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_pos_sourcePairSummand
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0)
    (hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_pos_sourcePairSummand
      hβpos n v e0 m hmpos hsummand_pos
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_data_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hmpos : 0 < d.1 e0) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  have hweight_pos :
      0 < edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) d :=
    edgeCopySourcePairDataWeight_pos_of_pos_on_support
      (FK.boxGraph 3 (2 * n)) hβpos (fun _ => 1) d
      (by intro e _he; norm_num)
  have hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) d.1 :=
    lt_of_lt_of_le hweight_pos
      (edgeCopySourcePairDataWeight_le_summand
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) d
        (le_of_lt hweight_pos))
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_pos_sourcePairSummand
      hβpos n v e0 d.1 hmpos hsummand_pos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_data_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))))
    (hmpos : 0 < d.1 e0) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_data_using_measuredEdge
      hβpos n v e0 d hmpos
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_fullSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  let d :=
    edgeCopySourcePairData_empty_of_fullSource
      (FK.boxGraph 3 (2 * n)) (doubledBoxOriginToInnerEndpointSource n v)
      m hfull
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_data_using_measuredEdge
      hβpos n v e0 d (by simpa [d] using hmpos)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_currentSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    exact hsrc
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_fullSource_using_measuredEdge
      hβpos n v e0 m hfull hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (he0 : 0 < p.1.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_path_count G p hov
  have hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G] using hsrc0
  have hmpos : 0 < m e0 := by
    simpa [G, m] using he0
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_currentSource_using_measuredEdge
      hβpos n v e0 m hsrc hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_forces_pathCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    p.1.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v e0 p hov (Nat.pos_of_ne_zero hne) hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_no_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.1.edges.count e0.1 := by
  rintro ⟨p, hp⟩
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v e0 p hov hp hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (he0 : 0 < p.1.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v e0 p hov he0
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_forces_pathCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    p.1.edges.count e0.1 = 0 :=
  doubledBoxSameBetaResidualEmptyBranchBound_forces_pathCount_eq_zero
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
    p hov

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_no_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.1.edges.count e0.1 :=
  doubledBoxSameBetaResidualEmptyBranchBound_no_pathCount_using_measuredEdge
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
    hov

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (he0 : 0 < p.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => p.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_walk_count G p hov
  have hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G] using hsrc0
  have hmpos : 0 < m e0 := by
    simpa [G, m] using he0
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_currentSource_using_measuredEdge
      hβpos n v e0 m hsrc hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_forces_walkCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    p.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v e0 p hov (Nat.pos_of_ne_zero hne) hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_no_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchBound β n v e0)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.edges.count e0.1 := by
  rintro ⟨p, hp⟩
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v e0 p hov hp hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (he0 : 0 < p.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v e0 p hov he0
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_forces_walkCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    p.edges.count e0.1 = 0 :=
  doubledBoxSameBetaResidualEmptyBranchBound_forces_walkCount_eq_zero
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
    p hov

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_no_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.edges.count e0.1 :=
  doubledBoxSameBetaResidualEmptyBranchBound_no_walkCount_using_measuredEdge
    hβpos n v e0
    (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)
    hov

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkThroughEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {x y : FK.boxVerts 3 (2 * n)}
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n)) x)
    (hxy : (FK.boxGraph 3 (2 * n)).Adj x y)
    (pRight :
      (FK.boxGraph 3 (2 * n)).Walk y
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedge : e0.1 = s(x, y))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ doubledBoxSameBetaResidualEmptyBranchBound β n v e0 := by
  let p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :=
    pLeft.append (SimpleGraph.Walk.cons hxy pRight)
  have he0 : 0 < p.edges.count e0.1 := by
    simpa [p] using
      walkThroughEdge_count_pos_of_edge_eq pLeft hxy pRight e0 hedge
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v e0 p hov he0

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_walkThroughEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {x y : FK.boxVerts 3 (2 * n)}
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n)) x)
    (hxy : (FK.boxGraph 3 (2 * n)).Adj x y)
    (pRight :
      (FK.boxGraph 3 (2 * n)).Walk y
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedge : e0.1 = s(x, y))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_walkThroughEdge_using_measuredEdge
      hβpos n v e0 pLeft hxy pRight hedge hov
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualEmptyBranchSourcePairBound_not_of_fullSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualEmptyBranchSourcePairBound β n v e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualEmptyBranchBound_not_of_fullSource_using_measuredEdge
      hβpos n v e0 m hfull hmpos
      (doubledBoxSameBetaResidualEmptyBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_forces_edgeMultiplicity_tsum_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m)) = 0 := by
  have hraw :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        β * (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m)) ≤
        β * edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
    simpa [doubledBoxSameBetaResidualInnerPairBranchBound,
      doubledBoxResidualMomentInnerPairBranchSummand] using hbound
  rw [tsum_mul_left] at hraw
  have hle :
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m)) ≤
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    le_of_mul_le_mul_left hraw hβpos
  exact
    edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_tsum_le_same_beta_forces_edgeMultiplicity_tsum_eq_zero
      (FK.boxGraph 3 (2 * n)) (le_of_lt hβpos) (fun _ => 1)
      (by intro e; norm_num) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) e0 hle

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_forces_edgeMultiplicity_tsum_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      (((m e0 : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m)) = 0 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_forces_edgeMultiplicity_tsum_eq_zero
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_forces_sourcePairSummand_eq_zero_of_pos
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m = 0 := by
  have hzero :=
    doubledBoxSameBetaResidualInnerPairBranchBound_forces_edgeMultiplicity_tsum_eq_zero
      hβpos n v w e0 hbound
  exact
    edgeMultiplicity_tsum_eq_zero_forces_sourcePairSummand_eq_zero_of_pos
      (FK.boxGraph 3 (2 * n)) (le_of_lt hβpos) (fun _ => 1)
      (by intro e; norm_num) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) e0 hzero m hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_forces_sourcePairSummand_eq_zero_of_pos
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0) :
    edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m = 0 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_forces_sourcePairSummand_eq_zero_of_pos
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
    m hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hsummand_ne :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m ≠ 0) :
    m e0 = 0 := by
  by_contra hmne
  have hmpos : 0 < m e0 := Nat.pos_of_ne_zero hmne
  have hzero :=
    doubledBoxSameBetaResidualInnerPairBranchBound_forces_sourcePairSummand_eq_zero_of_pos
      hβpos n v w e0 hbound m hmpos
  exact hsummand_ne hzero

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 ↔
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m ≠ 0 →
          m e0 = 0 := by
  constructor
  · intro hbound m hsummand_ne
    exact
      doubledBoxSameBetaResidualInnerPairBranchBound_forces_edgeMultiplicity_eq_zero_of_summand_ne_zero
        hβpos n v w e0 hbound m hsummand_ne
  · intro hsupport
    exact
      doubledBoxSameBetaResidualInnerPairBranchBound_of_support_zero β n v w e0
        (fun m hmne => by
          by_contra hsummand_ne
          exact hmne (hsupport m hsummand_ne))

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 ↔
      ∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m ≠ 0 →
          m e0 = 0 := by
  constructor
  · intro hbound
    exact
      (doubledBoxSameBetaResidualInnerPairBranchBound_iff_support_zero
        hβpos n v w e0).1
        (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
  · intro hsupport
    exact
      doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_of_support_zero
        β n v w e0
        (fun m hmne => by
          by_contra hsummand_ne
          exact hmne (hsupport m hsummand_ne))

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchBounds_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualBranchBounds β n v w e0 ↔
      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≠ 0 →
          m e0 = 0) ∧
      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m ≠ 0 →
          m e0 = 0) := by
  constructor
  · intro hbound
    constructor
    · exact
        (doubledBoxSameBetaResidualEmptyBranchBound_iff_support_zero
          hβpos n v e0).1 hbound.1
    · exact
        (doubledBoxSameBetaResidualInnerPairBranchBound_iff_support_zero
          hβpos n v w e0).1 hbound.2
  · rintro ⟨hempty, hinner⟩
    exact
      ⟨(doubledBoxSameBetaResidualEmptyBranchBound_iff_support_zero
          hβpos n v e0).2 hempty,
        (doubledBoxSameBetaResidualInnerPairBranchBound_iff_support_zero
          hβpos n v w e0).2 hinner⟩

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchSourcePairBounds_iff_support_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0 ↔
      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m ≠ 0 →
          m e0 = 0) ∧
      (∀ m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m ≠ 0 →
          m e0 = 0) := by
  constructor
  · intro hbound
    constructor
    · exact
        (doubledBoxSameBetaResidualEmptyBranchSourcePairBound_iff_support_zero
          hβpos n v e0).1 hbound.1
    · exact
        (doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_iff_support_zero
          hβpos n v w e0).1 hbound.2
  · rintro ⟨hempty, hinner⟩
    exact
      ⟨(doubledBoxSameBetaResidualEmptyBranchSourcePairBound_iff_support_zero
          hβpos n v e0).2 hempty,
        (doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_iff_support_zero
          hβpos n v w e0).2 hinner⟩

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pos_sourcePairSummand
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0)
    (hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  intro hbound
  have hzero :=
    doubledBoxSameBetaResidualInnerPairBranchBound_forces_sourcePairSummand_eq_zero_of_pos
      hβpos n v w e0 hbound m hmpos
  exact (ne_of_gt hsummand_pos) hzero

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_pos_sourcePairSummand
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hmpos : 0 < m e0)
    (hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pos_sourcePairSummand
      hβpos n v w e0 m hmpos hsummand_pos
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_data_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w))
    (hmpos : 0 < d.1 e0) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  have hweight_pos :
      0 < edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) d :=
    edgeCopySourcePairDataWeight_pos_of_pos_on_support
      (FK.boxGraph 3 (2 * n)) hβpos (fun _ => 1) d
      (by intro e _he; norm_num)
  have hsummand_pos :
      0 < edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) d.1 :=
    lt_of_lt_of_le hweight_pos
      (edgeCopySourcePairDataWeight_le_summand
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) d
        (le_of_lt hweight_pos))
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pos_sourcePairSummand
      hβpos n v w e0 d.1 hmpos hsummand_pos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_data_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w))
    (hmpos : 0 < d.1 e0) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_data_using_measuredEdge
      hβpos n v w e0 d hmpos
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_fullSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  let i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m :=
    ⟨e0, ⟨0, hmpos⟩⟩
  let K : Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m) :=
    (Finset.univ : Finset
      (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) \ {i}
  have hends :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) := by
    dsimp [i, Sharpness.FluxEdgeCopy.endsM]
    exact hedge
  have hends_swap :
      Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    dsimp [i, Sharpness.FluxEdgeCopy.endsM]
    rw [hedge, Sym2.eq_swap]
  have hsrcK :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m) K =
          doubledBoxOriginToInnerEndpointSource n w := by
    simpa [K, Finset.sdiff_singleton_eq_erase] using
      doubledBox_sources_remove_innerPairCopy
        (n := n) (v := w) (w := v) m
        (Finset.univ :
          Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m))
        (i := i) (Finset.mem_univ i) hfull hends_swap how hov
        (Ne.symm hvw)
  have hcomp :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) \
          K) =
          doubledBoxInnerPairSource n v w := by
    have hset :
        ((Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) \
          K) =
          ({i} :
            Finset (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [K]
      · simp [K, hji]
    rw [hset]
    have hsingle :=
      randomCurrent_sources_singleton_of_ends_eq
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        hends
    simpa [doubledBoxInnerPairSource] using hsingle
  let d :
      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) :=
    ⟨m, ⟨K, hsrcK, hcomp⟩⟩
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_data_using_measuredEdge
      hβpos n v w e0 d (by simpa [d] using hmpos)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_currentSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  have hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [Sharpness.FluxEdgeCopy.sources_eq,
      Sharpness.FluxEdgeCopy.profileFlux_univ]
    exact hsrc
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_fullSource_using_measuredEdge
      hβpos n v w e0 m hedge hov how hvw hfull hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (he0 : 0 < p.1.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_path_count G p hov
  have hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G] using hsrc0
  have hmpos : 0 < m e0 := by
    simpa [G, m] using he0
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_currentSource_using_measuredEdge
      hβpos n v w e0 m hedge hov how hvw hsrc hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_forces_pathCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    p.1.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw (Nat.pos_of_ne_zero hne)
      hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_no_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
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
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.1.edges.count e0.1 := by
  rintro ⟨p, hp⟩
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw hp hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (he0 : 0 < p.1.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_pathCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw he0
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_forces_pathCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    p.1.edges.count e0.1 = 0 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_forces_pathCount_eq_zero
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
    p hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_no_pathCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0)
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
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Path
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.1.edges.count e0.1 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_no_pathCount_using_measuredEdge
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
    hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (he0 : 0 < p.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  let G := FK.boxGraph 3 (2 * n)
  let m : ↥G.edgeFinset → ℕ := fun e => p.edges.count e.1
  have hsrc0 :
      Sharpness.sources G (Sharpness.ofEdgeFun G m) =
        ({IsingFK.boxOrigin 3 (2 * n),
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v} :
          Finset (FK.boxVerts 3 (2 * n))) := by
    simpa [G, m] using sources_ofEdgeFun_walk_count G p hov
  have hsrc :
      Sharpness.sources (FK.boxGraph 3 (2 * n))
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m) =
          doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simpa [G] using hsrc0
  have hmpos : 0 < m e0 := by
    simpa [G, m] using he0
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_currentSource_using_measuredEdge
      hβpos n v w e0 m hedge hov how hvw hsrc hmpos

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_forces_walkCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    p.edges.count e0.1 = 0 := by
  by_contra hne
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw (Nat.pos_of_ne_zero hne)
      hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_no_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0)
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
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.edges.count e0.1 := by
  rintro ⟨p, hp⟩
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw hp hbound

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (he0 : 0 < p.edges.count e0.1) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw he0
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_forces_walkCount_eq_zero
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0)
    (p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    p.edges.count e0.1 = 0 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_forces_walkCount_eq_zero
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
    p hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_no_walkCount_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound : doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0)
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
    ¬ ∃ p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v),
      0 < p.edges.count e0.1 :=
  doubledBoxSameBetaResidualInnerPairBranchBound_no_walkCount_using_measuredEdge
    hβpos n v w e0
    (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)
    hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkThroughEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {x y : FK.boxVerts 3 (2 * n)}
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n)) x)
    (hxy : (FK.boxGraph 3 (2 * n)).Adj x y)
    (pRight :
      (FK.boxGraph 3 (2 * n)).Walk y
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedgeRoute : e0.1 = s(x, y))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  let p :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :=
    pLeft.append (SimpleGraph.Walk.cons hxy pRight)
  have he0 : 0 < p.edges.count e0.1 := by
    simpa [p] using
      walkThroughEdge_count_pos_of_edge_eq pLeft hxy pRight e0 hedgeRoute
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkCount_using_measuredEdge
      hβpos n v w e0 p hedge hov how hvw he0

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_endpointEdgeWalk_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  have hedgeRoute :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
    rw [hedge, Sym2.eq_swap]
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkThroughEdge_using_measuredEdge
      hβpos n v w e0 pLeft hwv
      (SimpleGraph.Walk.nil :
        (FK.boxGraph 3 (2 * n)).Walk
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
      hedgeRoute hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_walkThroughEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    {x y : FK.boxVerts 3 (2 * n)}
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n)) x)
    (hxy : (FK.boxGraph 3 (2 * n)).Adj x y)
    (pRight :
      (FK.boxGraph 3 (2 * n)).Walk y
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedgeRoute : e0.1 = s(x, y))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_walkThroughEdge_using_measuredEdge
      hβpos n v w e0 pLeft hxy pRight hedgeRoute hedge hov how hvw
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_endpointEdgeWalk_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (pLeft :
      (FK.boxGraph 3 (2 * n)).Walk
        (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_endpointEdgeWalk_using_measuredEdge
      hβpos n v w e0 pLeft hwv hedge hov how hvw
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchBound_not_of_boxConnected_endpointEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchBound β n v w e0 := by
  rcases
      boxGraph_reachable 3 (2 * n) (IsingFK.boxOrigin 3 (2 * n))
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) with
    ⟨pLeft⟩
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_endpointEdgeWalk_using_measuredEdge
      hβpos n v w e0 pLeft hwv hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_boxConnected_endpointEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_boxConnected_endpointEdge_using_measuredEdge
      hβpos n v w e0 hwv hedge hov how hvw
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchBounds_not_of_boxConnected_endpointEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualBranchBounds β n v w e0 := by
  intro hbounds
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_boxConnected_endpointEdge_using_measuredEdge
      hβpos n v w e0 hwv hedge hov how hvw hbounds.2

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchSourcePairBounds_not_of_boxConnected_endpointEdge_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hwv :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
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
    ¬ doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0 := by
  intro hbounds
  exact
    doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_boxConnected_endpointEdge_using_measuredEdge
      hβpos n v w e0 hwv hedge hov how hvw hbounds.2

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    ¬ doubledBoxSameBetaResidualBranchBounds β n v w e0 := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨_edge, _hedge0, hov, how, hvw⟩
  exact
    doubledBoxSameBetaResidualBranchBounds_not_of_boxConnected_endpointEdge_using_measuredEdge
      hβpos n v w e0 hadj hedge hov how hvw

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualBranchSourcePairBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)) :
    ¬ doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0 := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨_edge, _hedge0, hov, how, hvw⟩
  exact
    doubledBoxSameBetaResidualBranchSourcePairBounds_not_of_boxConnected_endpointEdge_using_measuredEdge
      hβpos n v w e0 hadj hedge hov how hvw

set_option linter.style.longLine false in


theorem not_exists_doubledBoxSameBetaResidualBranchBounds_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    ¬ ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) ∧
        doubledBoxSameBetaResidualBranchBounds β n v w e0 := by
  rintro ⟨e0, hedge, hbounds⟩
  exact
    doubledBoxSameBetaResidualBranchBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
      hβpos e0 hvwedge hwwedge hheight hadj hedge hbounds

set_option linter.style.longLine false in


theorem not_exists_doubledBoxSameBetaResidualBranchSourcePairBounds_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    ¬ ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) ∧
        doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0 := by
  rintro ⟨e0, hedge, hbounds⟩
  exact
    doubledBoxSameBetaResidualBranchSourcePairBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
      hβpos e0 hvwedge hwwedge hheight hadj hedge hbounds

set_option linter.style.longLine false in


theorem not_forall_doubledBoxSameBetaResidualBranchBounds_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    ¬
      (∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          doubledBoxSameBetaResidualBranchBounds β n v w e0) := by
  intro hsame
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, _hov, _how, _hvw⟩
  exact
    doubledBoxSameBetaResidualBranchBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
      hβpos e0 hvwedge hwwedge hheight hadj hedge
      (hsame e0 hedge)

set_option linter.style.longLine false in


theorem not_forall_doubledBoxSameBetaResidualBranchSourcePairBounds_of_orderedWedge_lowerDoubledAdj_sameEdge
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    ¬
      (∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0) := by
  intro hsame
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, _hov, _how, _hvw⟩
  exact
    doubledBoxSameBetaResidualBranchSourcePairBounds_not_of_orderedWedge_lowerDoubledAdj_sameEdge
      hβpos e0 hvwedge hwwedge hheight hadj hedge
      (hsame e0 hedge)

set_option linter.style.longLine false in


theorem doubledBoxSameBetaResidualInnerPairBranchSourcePairBound_not_of_fullSource_using_measuredEdge
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hfull :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
        (Finset.univ : Finset
          (Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m)) =
          doubledBoxOriginToInnerEndpointSource n v)
    (hmpos : 0 < m e0) :
    ¬ doubledBoxSameBetaResidualInnerPairBranchSourcePairBound β n v w e0 := by
  intro hbound
  exact
    doubledBoxSameBetaResidualInnerPairBranchBound_not_of_fullSource_using_measuredEdge
      hβpos n v w e0 m hedge hov how hvw hfull hmpos
      (doubledBoxSameBetaResidualInnerPairBranchBound_of_sourcePairBound hbound)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_same_beta_edgeCopySourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsame :
      doubledBoxSameBetaResidualBranchBounds β n v w e0) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  let Sempty :=
    edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
  let Sinner :=
    edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
      (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
  rcases hsame with ⟨hempty, hinner⟩
  change
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (Sempty + Sinner)
  refine
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_branch_tsum_bounds_of_bounds
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (Cempty := β * Sempty) (Cinner := β * Sinner)
      (C := β * (Sempty + Sinner)) ?_ ?_ ?_
  · simpa [doubledBoxSameBetaResidualBranchBounds, Sempty] using hempty
  · simpa [doubledBoxSameBetaResidualBranchBounds, Sinner] using hinner
  · rw [mul_add]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_same_beta_sourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsame :
      doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  have hedgeCopy :
      β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
        β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) :=
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_same_beta_edgeCopySourcePairSums
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (doubledBoxSameBetaResidualBranchBounds_of_sourcePairBounds hsame)
  simpa [sourcePairSum_eq_edgeCopySourcePairSum] using hedgeCopy

set_option linter.style.longLine false in

theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_tsum_bound
    {β C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hsum :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentBranchSummand β n v w e0 m))
    (hbound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentBranchSummand β n v w e0 m) ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_tsum_bound
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hsum e0 hedge) (hbound e0 hedge)

set_option linter.style.longLine false in

theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_two_beta_sourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * β)
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_two_beta_sourcePairSums
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_residualMoment_branch_tsum_bounds
    {β Cempty Cinner C : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hempty :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m))
    (hinner :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
            doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m))
    (hempty_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentEmptyBranchSummand β n v e0 m) ≤ Cempty)
    (hinner_bound :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
            doubledBoxResidualMomentInnerPairBranchSummand β n v w e0 m) ≤ Cinner)
    (hbudget : Cempty + Cinner ≤ C) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤ C := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_residualMoment_branch_tsum_bounds
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hempty e0 hedge) (hinner e0 hedge)
      (hempty_bound e0 hedge) (hinner_bound e0 hedge) hbudget

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_same_beta_edgeCopySourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hsame :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          doubledBoxSameBetaResidualBranchBounds β n v w e0) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_same_beta_edgeCopySourcePairSums
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hsame e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_orderedWedge_lowerDoubledAdj_same_beta_sourcePairSums
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v))
    (hsame :
      ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        e0.1 =
            s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
              FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
          doubledBoxSameBetaResidualBranchSourcePairBounds β n v w e0) :
    β * doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum β n v ≤
      β * (Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_of_edgeIncrement_same_beta_sourcePairSums
      (n := n) (v := v) (w := w) e0 hβ hedge hov how hvw
      (hsame e0 hedge)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_orderedWedge_lowerDoubledAdj
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      β * (∑ m ∈ Ω,
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
        ∑ m' ∈ Ω.image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n w m' := by
  rcases
      doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
        hvwedge hwwedge hheight hadj with
    ⟨e0, hedge, hov, how, hvw⟩
  exact
    ⟨e0,
      beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul
        (n := n) (v := v) (w := w) Ω e0 hβ hedge hov how hvw⟩

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_strictSectorPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      β * (∑ m ∈ Ω,
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
        ∑ m' ∈ Ω.image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
              (boxVertStrictSectorPredecessor3 v hvwedge hlt) m' :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_orderedWedge_lowerDoubledAdj
    (n := n) (v := v)
    (w := boxVertStrictSectorPredecessor3 v hvwedge hlt)
    Ω hβ hvwedge
    (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
    (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
    (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_strictSectorYPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      β * (∑ m ∈ Ω,
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
        ∑ m' ∈ Ω.image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) m' :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_orderedWedge_lowerDoubledAdj
    (n := n) (v := v)
    (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    Ω hβ hvwedge
    (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
    (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
    (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_diagonalPredecessor3
    {β : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hβ : 0 ≤ β)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight_ne : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    ∃ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      β * (∑ m ∈ Ω,
          doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n v m) ≤
        ∑ m' ∈ Ω.image
            (fun m => Function.update m e0 (m e0 + 1)),
          ((m' e0 : ℕ) : ℝ) *
            doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β n
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
              m' :=
  beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm_finset_sum_le_edgeIncrement_image_count_mul_of_orderedWedge_lowerDoubledAdj
    (n := n) (v := v)
    (w := boxVertDiagonalPredecessor3 v hvwedge hheight_ne hnotlt)
    Ω hβ hvwedge
    (boxVertDiagonalPredecessor3_wedge v hvwedge hheight_ne hnotlt)
    (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight_ne hnotlt)
    (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
      (by omega : n ≤ 2 * n) v hvwedge hheight_ne hnotlt)

end Exact3D
end StatMech
