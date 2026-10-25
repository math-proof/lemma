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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part35
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    0 ≤ doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  have hJ : ∀ e : Sym2 (FK.boxVerts 3 (2 * n)), 0 ≤ (fun _ => (1 : ℝ)) e := by
    intro e
    exact zero_le_one
  have hcard :
      0 ≤
        (((edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card : ℕ) : ℝ) := by
    exact_mod_cast
      Nat.zero_le
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1)) e0).card
  have hleft :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m hβ hJ
  have hright :
      0 ≤
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) m := by
    exact
      edgeCopySourcePairSummand_nonneg (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m hβ hJ
  dsimp [doubledBoxSelectedCopyTotalPairCardSourcePairSummand]
  exact mul_nonneg hcard (add_nonneg hleft hright)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_origin_absent_on_copies
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ i : Sharpness.FluxEdgeCopy.Copy (FK.boxGraph 3 (2 * n)) m,
        IsingFK.boxOrigin 3 (2 * n) ∉
          Sharpness.FluxEdgeCopy.endsM (FK.boxGraph 3 (2 * n)) m i) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m = 0 := by
  have horigin_left_v :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n v := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair hov]
    simp
  have horigin_left_w :
      IsingFK.boxOrigin 3 (2 * n) ∈
        doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_v habsent
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_w habsent
  simp [doubledBoxSelectedCopyTotalPairCardSourcePairSummand, hleft, hright]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
        m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m = 0 :=
  doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_origin_absent_on_copies
    β e0 m hov how
    (fluxEdgeCopy_endsM_not_mem_of_edge_support_absent
      (FK.boxGraph 3 (2 * n)) habsent)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_selectedEdgeCopies_eq_zero
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
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0
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
  have horigin_left_w : o ∈ doubledBoxOriginToInnerEndpointSource n w := by
    rw [doubledBoxOriginToInnerEndpointSource_eq_pair how]
    simp [o]
  have hleft :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_v habsent
  have hright :
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) m = 0 :=
    edgeCopySourcePairSummand_eq_zero_of_left_source_vertex_absent
      (FK.boxGraph 3 (2 * n)) β (fun _ => 1) horigin_left_w habsent
  simp [doubledBoxSelectedCopyTotalPairCardSourcePairSummand, m, hleft, hright]

end Exact3D
end StatMech
