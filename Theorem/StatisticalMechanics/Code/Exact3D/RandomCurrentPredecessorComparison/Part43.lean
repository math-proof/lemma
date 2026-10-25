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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part41
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_owner_eq_some
    {n : ℕ} {A B : Finset (FK.boxVerts 3 (2 * n))}
    (fallback ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d : edgeCopySourcePairData (FK.boxGraph 3 (2 * n)) A B)
    (howner : doubledBoxOriginIncidentOwner n d.1 = some ew) :
    edgeCopySourcePairDataOriginIncidentOwnerTag (n := n)
      (A := A) (B := B) fallback d = ew := by
  simp [edgeCopySourcePairDataOriginIncidentOwnerTag, howner]

set_option linter.style.longLine false in


theorem edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_support_singleton
    {n : ℕ} {A B : Finset (FK.boxVerts 3 (2 * n))}
    (fallback ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (d : edgeCopySourcePairData (FK.boxGraph 3 (2 * n)) A B)
    (hsupport : doubledBoxOriginIncidentSupport n d.1 = {ew}) :
    edgeCopySourcePairDataOriginIncidentOwnerTag (n := n)
      (A := A) (B := B) fallback d = ew := by
  exact
    edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_owner_eq_some
      (n := n) (A := A) (B := B) fallback ew d
      (doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
        (n := n) (m := d.1) hsupport)

set_option linter.style.longLine false in


theorem doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
      m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1 := by
  intro e hme horigin
  exact hnot ⟨e, hme, horigin⟩

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hnot : ¬ doubledBoxOriginTouchesEdgeSupport n m) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m = 0 :=
  doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
    β e0 m hov how
    (doubledBoxOrigin_absent_on_edge_support_of_not_originTouchesEdgeSupport
      hnot)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_zeroOn_not_originTouchesEdgeSupport
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) :
    ∀ m ∈ Ω, ¬ doubledBoxOriginTouchesEdgeSupport n m →
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
        0 := by
  intro m _hm hnot
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
      β e0 m hov how hnot

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_zero_of_origin_absent_on_edge_support
    (β : ℝ) {n : ℕ} {v w : FK.boxVerts 3 n}
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (hov :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)
    (how :
      IsingFK.boxOrigin 3 (2 * n) ≠
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (habsent :
      ∀ m ∈ Ω,
        ∀ e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
          m e ≠ 0 → IsingFK.boxOrigin 3 (2 * n) ∉ e.1) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      0 := by
  refine Finset.sum_eq_zero ?_
  intro m hm
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_zero_of_origin_absent_on_edge_support
      β e0 m hov how (habsent m hm)

set_option linter.style.longLine false in

theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_singleton_selectedEdgeCopies_sum_eq_zero
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
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      0 := by
  simp [doubledBoxSelectedEdgeCopiesSingletonCutoff,
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_selectedEdgeCopies_eq_zero
      β e0 k hedge hov how]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_nonneg
    {β : ℝ} {n : ℕ} {v w : FK.boxVerts 3 n}
    (hβ : 0 ≤ β)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)) :
    0 ≤ ∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m := by
  exact
    Finset.sum_nonneg (fun m _hm =>
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand_nonneg
        (n := n) (v := v) (w := w) hβ e0 m)

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ
    (n : ℕ) (w : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card =
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1))).card *
        (m e0 + 1) := by
  rw [edgeCopySourceSectorSelectedEdgeCopyPairs_card]
  simp

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sum_sourcePairWitnesses_card_mul_succ
    (n : ℕ) (w : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (Function.update m e0 (m e0 + 1)) e0).card =
      (∑ B : Finset (FK.boxVerts 3 (2 * n)),
        (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) B
          (Function.update m e0 (m e0 + 1))).card) *
        (m e0 + 1) := by
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]
  rw [edgeCopySourceSector_card_eq_sum_sourcePairWitnesses_card]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sourceSector_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (Function.update m e0 (m e0 + 1))).card * (m e0 + 1) : ℕ) : ℝ) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  dsimp [doubledBoxSelectedCopyTotalPairCardSourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sourceSector_card_mul_succ]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sum_sourcePairWitnesses_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m =
      (((∑ B : Finset (FK.boxVerts 3 (2 * n)),
          (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) B
            (Function.update m e0 (m e0 + 1))).card) *
          (m e0 + 1) : ℕ) : ℝ) *
        (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) m) := by
  dsimp [doubledBoxSelectedCopyTotalPairCardSourcePairSummand]
  rw [doubledBoxSelectedCopyPairCard_edgeIncrement_eq_sum_sourcePairWitnesses_card_mul_succ]

set_option linter.style.longLine false in


theorem doubledBoxSelectedCopyTotalPairCardSourcePairSummand_finset_sum_eq_sum_sourcePairWitnesses_card_mul_succ
    (β : ℝ) (n : ℕ) (v w : FK.boxVerts 3 n)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :
    (∑ m ∈ Ω,
      doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v w e0 m) =
      ∑ m ∈ Ω,
        (((∑ B : Finset (FK.boxVerts 3 (2 * n)),
            (edgeCopySourcePairWitnesses (FK.boxGraph 3 (2 * n))
              (doubledBoxOriginToInnerEndpointSource n w) B
              (Function.update m e0 (m e0 + 1))).card) *
            (m e0 + 1) : ℕ) : ℝ) *
          (edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) m +
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) m) := by
  refine Finset.sum_congr rfl ?_
  intro m _hm
  exact
    doubledBoxSelectedCopyTotalPairCardSourcePairSummand_eq_sum_sourcePairWitnesses_card_mul_succ
      β n v w e0 m

end Exact3D
end StatMech
