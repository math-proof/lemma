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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part32
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage_weight_sum_le_sourcePairEmptySum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  classical
  simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum] using
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
      (G := FK.boxGraph 3 (2 * n)) (β := β) hβ
      (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
      (doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
        m e0 hedge hfull hov how hvw)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) := by
  classical
  simpa using
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
      (G := FK.boxGraph 3 (2 * n)) (β := β) hβ
      (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage
        m e0 hedge hfull hov how hvw)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage_weight_sum_le_sourcePairEmptySum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  classical
  simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum] using
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
      (G := FK.boxGraph 3 (2 * n)) (β := β) hβ
      (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n)))
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage
        m e0 hedge hfull hov how hvw)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxInnerPairSource n v w)
        (doubledBoxOriginToInnerEndpointSource n w) := by
  classical
  simpa using
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
      (G := FK.boxGraph 3 (2 * n)) (β := β) hβ
      (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
        m e0 hedge hfull hov how hvw)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage_weight_sum_le_orientedSourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) := by
  have h :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  have hcomm :=
    sourcePairSum_comm (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxInnerPairSource n v w)
      (doubledBoxOriginToInnerEndpointSource n w)
  simpa [hcomm] using h

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsInCurrent_innerPairOutside_decrementSourcePairDataImage_weight_sum_le_sourcePairSplitScalar
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) +
      (∑ d ∈
          doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
            m e0 hedge hfull hov how hvw,
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d) ≤
        doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w := by
  have hin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage_weight_sum_le_sourcePairEmptySum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  have hout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage_weight_sum_le_orientedSourcePairSum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
    add_le_add hin hout

set_option linter.style.longLine false in


theorem
    beta_mul_doubledBox_selectedEdgeCopyPairsInCurrent_innerPairOutside_decrementSourcePairDataImage_weight_sum_le_selectedCopySplitBound
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    β *
      ((∑ d ∈
          doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
            m e0 hedge hfull hov how hvw,
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d) +
        (∑ d ∈
            doubledBox_selectedEdgeCopyPairsOutsideCurrent_innerPairSource_decrementSourcePairDataImage
              m e0 hedge hfull hov how hvw,
          edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
            (fun _ => (1 : ℝ)) d)) ≤
        doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w := by
  have hsplit :=
    doubledBox_selectedEdgeCopyPairsInCurrent_innerPairOutside_decrementSourcePairDataImage_weight_sum_le_sourcePairSplitScalar
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  simpa [doubledBoxOriginToInnerEndpointSelectedCopySplitBound] using
    mul_le_mul_of_nonneg_left hsplit hβ

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) ≤
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) := by
  classical
  simpa using
    edgeCopySourcePairDataWeight_finset_sum_le_sourcePairSum
      (G := FK.boxGraph 3 (2 * n)) (β := β) hβ
      (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w)
      (doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage
        m e0 hedge hfull hov how hvw)

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairs_decrementSourcePairDataImage_weight_sum_le_sourcePairSplitScalar
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) +
      (∑ d ∈
          doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage
            m e0 hedge hfull hov how hvw,
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d) ≤
        doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w := by
  have hin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_decrementSourcePairDataImage_weight_sum_le_sourcePairEmptySum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  have hout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
    add_le_add hin hout

set_option linter.style.longLine false in


theorem
    doubledBox_selectedEdgeCopyPairs_switched_decrementSourcePairDataImage_weight_sum_le_sourcePairSplitScalar
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hfull :
      Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m)
          (Finset.univ :
            Finset (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n)) m)) =
        doubledBoxOriginToInnerEndpointSource n w)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hvw :
      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ d ∈
        doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage
          m e0 hedge hfull hov how hvw,
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
        (fun _ => (1 : ℝ)) d) +
      (∑ d ∈
          doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage
            m e0 hedge hfull hov how hvw,
        edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
          (fun _ => (1 : ℝ)) d) ≤
        doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w := by
  have hout :=
    doubledBox_selectedEdgeCopyPairsOutsideCurrent_switched_decrementSourcePairDataImage_weight_sum_le_sourcePairEmptySum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  have hin :=
    doubledBox_selectedEdgeCopyPairsInCurrent_switched_decrementSourcePairDataImage_weight_sum_le_sourcePairSum
      (n := n) (v := v) (w := w) hβ m e0 hedge hfull hov how hvw
  simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
    add_le_add hout hin

set_option linter.style.longLine false in

theorem doubledBoxOriginToInnerEndpointSourcePairSplitScalar_eq_currentSum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n) :
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w =
      doubledBoxOriginToInnerEndpointCurrentSum β n v *
          Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        doubledBoxOriginToInnerEndpointCurrentSum β n w *
          Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w) := by
  unfold doubledBoxOriginToInnerEndpointSourcePairSplitScalar
    doubledBoxOriginToInnerEndpointSourcePairEmptySum
    doubledBoxOriginToInnerEndpointCurrentSum
  rw [Sharpness.sourcePairSum_eq_mul]
  rw [Sharpness.sourcePairSum_eq_mul]

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_currentSum_product_split_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hcurrent :
      doubledBoxOriginToInnerEndpointCurrentSum β n v *
          Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        doubledBoxOriginToInnerEndpointCurrentSum β n w *
          Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w) ≤
        doubledBoxOriginToInnerEndpointCurrentSum β n w *
          Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))) :
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
  rw [doubledBoxOriginToInnerEndpointSourcePairSplitScalar_eq_currentSum]
  rw [doubledBoxOriginToInnerEndpointSourcePairEmptySum,
    Sharpness.sourcePairSum_eq_mul, doubledBoxOriginToInnerEndpointCurrentSum]
  exact hcurrent

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_currentSum_expectationJ_split_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hcurrentJ :
      doubledBoxOriginToInnerEndpointCurrentSum β n v +
          doubledBoxOriginToInnerEndpointCurrentSum β n w *
            Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxInnerPairSource n v w) ≤
        doubledBoxOriginToInnerEndpointCurrentSum β n w) :
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w :=
  sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_currentSum_expectationJ_split_le
    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n v)
    (doubledBoxOriginToInnerEndpointSource n w)
    (doubledBoxInnerPairSource n v w) hcurrentJ

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_expectationJ_split_le
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hJ :
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v) +
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w) *
          Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxInnerPairSource n v w) ≤
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)) :
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
  simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar,
    doubledBoxOriginToInnerEndpointSourcePairEmptySum] using
    sourcePairSum_empty_add_sourcePairSum_le_sourcePairSum_empty_of_expectationJ_split_le
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) hJ

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_expectationJ_ratio_gap
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hpos :
      0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w))
    (hratio :
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v) /
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w) +
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxInnerPairSource n v w) ≤ 1) :
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w :=
  doubledBoxOriginToInnerEndpointSourcePairSplitScalar_le_sourcePairEmptySum_of_expectationJ_split_le
    (expectationJ_split_le_of_ratio_add_le_one hpos hratio)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSelectedCopySplitBound_le_beta_mul_sourcePairEmptySum_of_sourcePairSplit_le
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (hsplit :
      doubledBoxOriginToInnerEndpointSourcePairSplitScalar β n v w ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w) :
    doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w ≤
      β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n w := by
  dsimp [doubledBoxOriginToInnerEndpointSelectedCopySplitBound]
  exact mul_le_mul_of_nonneg_left hsplit hβ

set_option linter.style.longLine false in

theorem doubledBoxOriginToInnerEndpointSelectedCopySplitBound_eq_currentSum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n) :
    doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v w =
      β *
        (doubledBoxOriginToInnerEndpointCurrentSum β n v *
            Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          doubledBoxOriginToInnerEndpointCurrentSum β n w *
            Sharpness.currentSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxInnerPairSource n v w)) := by
  unfold doubledBoxOriginToInnerEndpointSelectedCopySplitBound
    doubledBoxOriginToInnerEndpointSourcePairSplitScalar
    doubledBoxOriginToInnerEndpointSourcePairEmptySum
    doubledBoxOriginToInnerEndpointCurrentSum
  rw [Sharpness.sourcePairSum_eq_mul]
  rw [Sharpness.sourcePairSum_eq_mul]

end Exact3D
end StatMech
