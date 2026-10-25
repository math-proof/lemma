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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part43
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_empty_add_inner
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m +
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m := by
  rw [doubledBoxSelectedCopyTotalPairCardSourcePairSummand,
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand,
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
      m := by
  dsimp [doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m := by
  dsimp [doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand]
  exact
    mul_nonneg (by positivity)
      (edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ
        (by intro e; norm_num))

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
      0 := by
  have horigin_left_v :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simp
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_v habsent
  simp [doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand, hleft]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
      0 :=
  doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_copies
    β e0 m hov
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let o := IsingFK.boxOrigin 3 (2 * n)
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have horigin_not_mem_e0 : o ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, o, hov, how]
  have habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        o ∉ Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i := by
    intro i
    have hends :
        Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i = e0.1 := by
      simpa [m] using
        fluxEdgeCopy_endsM_singleEdgeCopies_eq
          (FK.boxGraph 3 (2 * n)) e0 k i
    simpa [hends] using horigin_not_mem_e0
  have horigin_left_v : o ∈ doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simp [o]
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_v habsent
  simp [doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand, m, hleft]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0
        m =
      0 := by
  have horigin_left_w :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_w habsent
  simp [doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand, hright]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0
        m =
      0 :=
  doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_copies
    β e0 m how
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0
      (Function.update
        (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k) = 0 := by
  let o := IsingFK.boxOrigin 3 (2 * n)
  let m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update (fun _ : ↥(FK.boxGraph 3 (2 * n)).edgeFinset => 0) e0 k
  have horigin_not_mem_e0 : o ∉ e0.1 := by
    rw [hedge]
    simp [Sym2.mem_iff, o, hov, how]
  have habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        o ∉ Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i := by
    intro i
    have hends :
        Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i = e0.1 := by
      simpa [m] using
        fluxEdgeCopy_endsM_singleEdgeCopies_eq
          (FK.boxGraph 3 (2 * n)) e0 k i
    simpa [hends] using horigin_not_mem_e0
  have horigin_left_w : o ∈ doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp [o]
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_w habsent
  simp [doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand, m,
    hright]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
      0 :=
  doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m hov
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0
        m =
      0 :=
  doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m how
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_originIncidentSupport_eq_empty
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hsupport : doubledBoxOriginIncidentSupport n m = ∅) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
      0 := by
  apply
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov
  intro htouch
  have hnonempty :
      (doubledBoxOriginIncidentSupport n m).Nonempty :=
    (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport).2
      htouch
  simp [hsupport] at hnonempty

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_originIncidentSupport_eq_empty
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsupport : doubledBoxOriginIncidentSupport n m = ∅) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0
        m =
      0 := by
  apply
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how
  intro htouch
  have hnonempty :
      (doubledBoxOriginIncidentSupport n m).Nonempty :=
    (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport).2
      htouch
  simp [hsupport] at hnonempty

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m hov (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m how (habsent m hm)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ m ∈ doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k,
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
        m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_selectedEdgeCopies_eq_zero
      β e0 k hedge hov how]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) (k : ℕ)
    (hedge :
      e0.1 =
        s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    (∑ m ∈ doubledBoxSelectedEdgeCopiesSingletonCutoff n e0 k,
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_selectedEdgeCopies_eq_zero
      β e0 k hedge hov how]

set_option linter.style.longLine false in

theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSector_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  dsimp [doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]

set_option linter.style.longLine false in

theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSector_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) : ℕ) : ℝ) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  dsimp [doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSectorResidualMomentEmptyBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m =
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m := by
  rw [doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSector_card_mul_succ]
  dsimp [doubledBoxSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxResidualMomentEmptyBranchSummand]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSectorResidualMomentInnerPairBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β *
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m =
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0
        m := by
  rw [doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSector_card_mul_succ]
  dsimp [doubledBoxSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentInnerPairBranchSummand]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in

theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_totalPairCardEmptySourcePairSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m =
      β *
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m :=
  (beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSectorResidualMomentEmptyBranchSummand
    β n v w e0 m).symm

set_option linter.style.longLine false in

theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_totalPairCardInnerPairSourcePairSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m =
      β *
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m :=
  (beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSectorResidualMomentInnerPairBranchSummand
    β n v w e0 m).symm

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m =
      0 := by
  rw [doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_totalPairCardEmptySourcePairSummand]
  rw [
    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m =
      0 := by
  rw [doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_totalPairCardInnerPairSourcePairSummand]
  rw [
    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot]
  ring

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov hnot

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m how hnot

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m := by
  dsimp [doubledBoxSourceSectorResidualMomentEmptyBranchSummand]
  exact
    mul_nonneg (by positivity)
      (doubledBoxResidualMomentEmptyBranchSummand_nonneg
        (n := n) (v := v) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m := by
  dsimp [doubledBoxSourceSectorResidualMomentInnerPairBranchSummand]
  exact
    mul_nonneg (by positivity)
      (doubledBoxResidualMomentInnerPairBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m := by
  rw [doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
  exact
    add_nonneg
      (doubledBoxSourceSectorResidualMomentEmptyBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)
      (doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m ≤
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
  let G := FK.boxGraph 3 (2 * n)
  let S := doubledBoxOriginToInnerEndpointSource n w
  let A := doubledBoxOriginToInnerEndpointSource n v
  have hdom :
      ((edgeCopySourceSector G S
        (Function.update m e0 (m e0 + 1))).card : ℝ) *
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) ≤
        2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m :=
    edgeCopySourceSector_card_update_succ_mul_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_mul_four_beta
      G hβ S A (∅ : Finset (FK.boxVerts 3 (2 * n))) m e0
  dsimp [doubledBoxSourceSectorResidualMomentEmptyBranchSummand,
    doubledBoxResidualMomentEmptyBranchSummand]
  change
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
      (β * (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) ≤
      (2 * β) *
        edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  calc
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
        (β * (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) =
        β *
          (((edgeCopySourceSector G S
            (Function.update m e0 (m e0 + 1))).card : ℝ) *
            (((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1) A
                (∅ : Finset (FK.boxVerts 3 (2 * n))) m)) := by
      ring
    _ ≤ β *
          (2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) := by
      exact mul_le_mul_of_nonneg_left hdom hβ
    _ =
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m ≤
      (2 * β) *
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
  let G := FK.boxGraph 3 (2 * n)
  let S := doubledBoxOriginToInnerEndpointSource n w
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  have hdom :
      ((edgeCopySourceSector G S
        (Function.update m e0 (m e0 + 1))).card : ℝ) *
        (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A B m) ≤
        2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m :=
    edgeCopySourceSector_card_update_succ_mul_edgeMultiplicitySucc_mul_edgeCopySourcePairSummand_le_two_mul_four_beta
      G hβ S A B m e0
  dsimp [doubledBoxSourceSectorResidualMomentInnerPairBranchSummand,
    doubledBoxResidualMomentInnerPairBranchSummand]
  change
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
      (β * (((m e0 + 1 : ℕ) : ℝ) *
        edgeCopySourcePairSummand G β (fun _ => 1) A B m)) ≤
      (2 * β) *
        edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m
  calc
    ((edgeCopySourceSector G S
      (Function.update m e0 (m e0 + 1))).card : ℝ) *
        (β * (((m e0 + 1 : ℕ) : ℝ) *
          edgeCopySourcePairSummand G β (fun _ => 1) A B m)) =
        β *
          (((edgeCopySourceSector G S
            (Function.update m e0 (m e0 + 1))).card : ℝ) *
            (((m e0 + 1 : ℕ) : ℝ) *
              edgeCopySourcePairSummand G β (fun _ => 1) A B m)) := by
      ring
    _ ≤ β *
          (2 * edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m) := by
      exact mul_le_mul_of_nonneg_left hdom hβ
    _ =
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m := by
      ring

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m) :=
    (edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A
      (∅ : Finset (FK.boxVerts 3 (2 * n)))).mul_left (2 * β)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    exact
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m
  · intro m
    exact
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
        hβ n v w e0 m

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  have hdom :
      Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        (2 * β) *
          edgeCopySourcePairSummand G (2 * (2 * β)) (fun _ => 1) A B m) :=
    (edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A B).mul_left
      (2 * β)
  refine Summable.of_nonneg_of_le ?hnonneg ?hle hdom
  · intro m
    exact
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m
  · intro m
    exact
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
        hβ n v w e0 m

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_summable_of_nonneg_beta
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) := by
  have hempty :=
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hinner :=
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  simpa [doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
    using hempty.add hinner

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentEmptyBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n v
  rw [edgeCopySourcePairSum, ← tsum_mul_left]
  exact
    (doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0).tsum_le_tsum
      (fun m =>
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
          hβ n v w e0 m)
      ((edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A
        (∅ : Finset (FK.boxVerts 3 (2 * n)))).mul_left (2 * β))

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m) ≤
      (2 * β) *
        edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let B := doubledBoxInnerPairSource n v w
  rw [edgeCopySourcePairSum, ← tsum_mul_left]
  exact
    (doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0).tsum_le_tsum
      (fun m =>
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_le_two_beta_mul_four_beta_sourcePairSummand
          hβ n v w e0 m)
      ((edgeCopySourcePairSummand_summable G (2 * (2 * β)) (fun _ => 1) A B).mul_left
        (2 * β))

set_option linter.style.longLine false in


theorem doubledBoxSourceSectorResidualMomentBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSums
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) ≤
      (2 * β) *
        (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) +
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) := by
  have hempty_summable :=
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hinner_summable :=
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
      hβ n v w e0
  have hempty :=
    doubledBoxSourceSectorResidualMomentEmptyBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0
  have hinner :=
    doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
      hβ n v w e0
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) =
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) +
        (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
            e0 m) := by
      conv_lhs =>
        congr
        intro m
        rw [doubledBoxSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
      exact Summable.tsum_add hempty_summable hinner_summable
    _ ≤
        (2 * β) *
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
        (2 * β) *
          edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
      add_le_add hempty hinner
    _ =
        (2 * β) *
          (edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) +
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) := by
      ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_residualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  rw [doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_succ]
  dsimp [doubledBoxResidualMomentBranchSummand]
  rw [Nat.cast_mul]
  ring

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSectorResidualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m := by
  simpa [doubledBoxSourceSectorResidualMomentBranchSummand] using
    beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_residualMomentBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in

theorem doubledBoxSourceSectorResidualMomentBranchSummand_eq_beta_mul_totalPairCardSourcePairSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m =
      β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m :=
  (beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSectorResidualMomentBranchSummand
    β n v w e0 m).symm

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sum_sourcePairWitnesses_card_mul_residualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    β * doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (((∑ B : Finset (FK.boxVerts 3 (2 * n)),
          (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) B
            (Function.update m e0 (m e0 + 1))).card) : ℕ) : ℝ) *
        doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  rw [
    beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_residualMomentBranchSummand]
  rw [edgeCopySourceSector_card_eq_sum_sourcePairWitnesses_card]

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sourceSector_card_mul_residualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w)
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_residualMomentBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sourceSectorResidualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSectorResidualMomentBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_sourceSectorResidualMomentEmptyBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
        m) =
      ∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0
          m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSectorResidualMomentEmptyBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_sourceSectorResidualMomentInnerPairBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) =
      ∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSectorResidualMomentInnerPairBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_le_of_sourceSectorResidualMomentEmptyBranchSummand_sum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0
          m) ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
        m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  have hmul :
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m) ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    calc
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w e0
          m) =
          ∑ m ∈ Ω,
            doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w
              e0 m :=
            beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_finset_sum_eq_sourceSectorResidualMomentEmptyBranchSummand
              β n v w Ω e0
      _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_le_of_sourceSectorResidualMomentInnerPairBranchSummand_sum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
          e0 m) ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
        e0 m) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
  have hmul :
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m) ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
    calc
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v w
          e0 m) =
          ∑ m ∈ Ω,
            doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w
              e0 m :=
            beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_finset_sum_eq_sourceSectorResidualMomentInnerPairBranchSummand
              β n v w Ω e0
      _ ≤
          β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_le_of_sourceSectorResidualMomentBranchSummand_sum_bound
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 < β)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hbound :
      (∑ m ∈ Ω,
        doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
  have hmul :
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) ≤
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) := by
    calc
      β * (∑ m ∈ Ω,
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
          ∑ m ∈ Ω,
            doubledBoxSourceSectorResidualMomentBranchSummand β n v w e0 m :=
            beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sourceSectorResidualMomentBranchSummand
              β n v w Ω e0
      _ ≤
          β *
            (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
              Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w)) :=
        hbound
  exact le_of_mul_le_mul_left hmul hβ

set_option linter.style.longLine false in


theorem beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sum_sourcePairWitnesses_card_mul_residualMomentBranchSummand
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    β * (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (((∑ B : Finset (FK.boxVerts 3 (2 * n)),
            (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) B
              (Function.update m e0 (m e0 + 1))).card) : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    beta_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sum_sourcePairWitnesses_card_mul_residualMomentBranchSummand
      β n v w e0 m

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_allComplementSourcePairSummand_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1))) *
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (((m e0 + 1 : ℕ) : ℝ) *
        (∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w) B
            (Function.update m e0 (m e0 + 1)))) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let Wleft :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let Wright :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hsector :
      ((edgeCopySourceSector G A M).card : ℝ) *
          Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G M) =
        ∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSummand G β (fun _ => 1) A B M := by
    exact
      edgeCopySourceSector_card_mul_weight_eq_sum_sourcePairSummand
        G β (fun _ => 1) A M
  rw [doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_succ]
  change
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G M) *
      ((((edgeCopySourceSector G A M).card * (m e0 + 1) : ℕ) : ℝ) *
        (Wleft + Wright)) =
      (((m e0 + 1 : ℕ) : ℝ) *
        (∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSummand G β (fun _ => 1) A B M)) *
        (Wleft + Wright)
  rw [Nat.cast_mul]
  calc
    Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G M) *
      ((((edgeCopySourceSector G A M).card : ℝ) *
          ((m e0 + 1 : ℕ) : ℝ)) * (Wleft + Wright)) =
        (((m e0 + 1 : ℕ) : ℝ) *
          (((edgeCopySourceSector G A M).card : ℝ) *
            Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G M))) *
          (Wleft + Wright) := by
      ring
    _ =
        (((m e0 + 1 : ℕ) : ℝ) *
          (∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSummand G β (fun _ => 1) A B M)) *
          (Wleft + Wright) := by
      rw [hsector]

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_allComplementSourcePairSummand_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (((m e0 + 1 : ℕ) : ℝ) *
          (∑ B : Finset (FK.boxVerts 3 (2 * n)),
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w) B
              (Function.update m e0 (m e0 + 1)))) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_allComplementSourcePairSummand_sum
      β n v w e0 m

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeight_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
          (Function.update m e0 (m e0 + 1))) *
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (β *
        (∑ B : Finset (FK.boxVerts 3 (2 * n)),
          (((edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) B
            (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
            Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  let G := FK.boxGraph 3 (2 * n)
  let A := doubledBoxOriginToInnerEndpointSource n w
  let M : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ :=
    Function.update m e0 (m e0 + 1)
  let Wleft :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n v)
      (∅ : Finset (FK.boxVerts 3 (2 * n))) m
  let Wright :=
    edgeCopySourcePairSummand G β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n w)
      (doubledBoxInnerPairSource n v w) m
  have hshift :
      (((m e0 + 1 : ℕ) : ℝ) *
        (∑ B : Finset (FK.boxVerts 3 (2 * n)),
          edgeCopySourcePairSummand G β (fun _ => 1) A B M)) =
        β *
          (∑ B : Finset (FK.boxVerts 3 (2 * n)),
            (((edgeCopySourcePairWitnesses G A B M).card : ℕ) : ℝ) *
              Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m)) := by
    simpa [G, A, M] using
      edgeMultiplicitySucc_mul_sum_edgeCopySourcePairSummand_increment_eq_betaJ_mul_sum_sourcePairWitnesses_card_mul_weight
        (FK.boxGraph 3 (2 * n)) β (fun _ => 1) A m e0
  rw [weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_allComplementSourcePairSummand_sum]
  change
    ((((m e0 + 1 : ℕ) : ℝ) *
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        edgeCopySourcePairSummand G β (fun _ => 1) A B M)) *
        (Wleft + Wright)) =
      (β *
        (∑ B : Finset (FK.boxVerts 3 (2 * n)),
          (((edgeCopySourcePairWitnesses G A B M).card : ℕ) : ℝ) *
            Sharpness.weight G β (fun _ => 1) (Sharpness.ofEdgeFun G m))) *
        (Wleft + Wright)
  rw [hshift]

set_option linter.style.longLine false in


theorem weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_beta_mul_allComplementWitnessCardWeight_sum
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n))
            (Function.update m e0 (m e0 + 1))) *
        doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (β *
          (∑ B : Finset (FK.boxVerts 3 (2 * n)),
            (((edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) B
              (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
              Sharpness.weight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (Sharpness.ofEdgeFun (FK.boxGraph 3 (2 * n)) m))) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    weight_increment_mul_doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_beta_mul_allComplementWitnessCardWeight_sum
      β n v w e0 m

end Exact3D
end StatMech
