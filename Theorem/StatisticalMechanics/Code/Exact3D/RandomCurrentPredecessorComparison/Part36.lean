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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part34
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyBranchCardSourcePairSummand_le_switchedSourceSectorResidualMomentBranchSummand
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1)))
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))) =
        doubledBoxOriginToInnerEndpointSource n w)
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
    β * doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m ≤
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  classical
  let G := FK.boxGraph 3 (2 * n)
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let C : ℝ :=
    (((edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v)
      M).card : ℕ) : ℝ)
  let N : ℝ := (((m e0 + 1 : ℕ) : ℕ) : ℝ)
  let Sin :=
    edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent G
      (doubledBoxOriginToInnerEndpointSource n w) M e0
  let Sout :=
    edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent G
      (doubledBoxOriginToInnerEndpointSource n w) M e0
  let X :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let Y :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hSin_nat :
      Sin.card ≤
        (edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v)
          M).card * (m e0 + 1) := by
    simpa [Sin, G, M] using
      doubledBox_selectedEdgeCopyPairsInCurrent_card_le_switchedSourceSector_card_mul_succ
        (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw
  have hSout_nat :
      Sout.card ≤
        (edgeCopySourceSector G (doubledBoxOriginToInnerEndpointSource n v)
          M).card * (m e0 + 1) := by
    simpa [Sout, G, M] using
      doubledBox_selectedEdgeCopyPairsOutsideCurrent_card_le_switchedSourceSector_card_mul_succ
        (n := n) (v := v) (w := w) m e0 hfull hedge hov how hvw
  have hSin :
      (Sin.card : ℝ) ≤ C * N := by
    have hcast :
        (Sin.card : ℝ) ≤
          (((edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M).card *
            (m e0 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hSin_nat
    have hmul :
        (((edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M).card *
            (m e0 + 1) : ℕ) : ℝ) = C * N := by
      simp [C, N, Nat.cast_mul]
    exact hcast.trans_eq hmul
  have hSout :
      (Sout.card : ℝ) ≤ C * N := by
    have hcast :
        (Sout.card : ℝ) ≤
          (((edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M).card *
            (m e0 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hSout_nat
    have hmul :
        (((edgeCopySourceSector G
              (doubledBoxOriginToInnerEndpointSource n v) M).card *
            (m e0 + 1) : ℕ) : ℝ) = C * N := by
      simp [C, N, Nat.cast_mul]
    exact hcast.trans_eq hmul
  have hX : 0 ≤ X := by
    dsimp [X, G]
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num)
  have hY : 0 ≤ Y := by
    dsimp [Y, G]
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num)
  have hbranch :
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m ≤
        C * (N * X + N * Y) := by
    change (Sin.card : ℝ) * X + (Sout.card : ℝ) * Y ≤
      C * (N * X + N * Y)
    calc
      (Sin.card : ℝ) * X + (Sout.card : ℝ) * Y ≤
          (C * N) * X + (C * N) * Y := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hSin hX)
          (mul_le_mul_of_nonneg_right hSout hY)
      _ = C * (N * X + N * Y) := by ring
  calc
    β * doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m ≤
        β * (C * (N * X + N * Y)) :=
      mul_le_mul_of_nonneg_left hbranch hβ
    _ =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      dsimp [doubledBoxResidualMomentBranchSummand, G, M, C, N, X, Y]
      ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyBranchCardSourcePairSummand_finset_sum_le_switchedSourceSectorResidualMomentBranchSummand_sum
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hfull :
      ∀ m ∈ Ω,
        Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n))
              (Function.update m e0 (m e0 + 1)))
            (Finset.univ :
              Finset (Sharpness.FluxEdgeCopy.Copy
                (FK.boxGraph 3 (2 * n))
                (Function.update m e0 (m e0 + 1)))) =
          doubledBoxOriginToInnerEndpointSource n w)
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
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) ≤
      ∑ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  calc
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m) =
        ∑ m ∈ Ω,
          β * doubledBoxSelectedCopyBranchCardSourcePairSummand β n v w e0 m := by
      rw [Finset.mul_sum]
    _ ≤
      ∑ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact
        beta_mul_doubledBoxSelectedCopyBranchCardSourcePairSummand_le_switchedSourceSectorResidualMomentBranchSummand
          (n := n) (v := v) (w := w) hβ m e0 (hfull m hm)
          hedge hov how hvw

end Exact3D
end StatMech
