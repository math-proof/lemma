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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part24
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_le_of_predecessorSourceSector_card
    {n : ℕ} {v w : FK.boxVerts 3 n}
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
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card ≤
      (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card := by
  have hAB :
      doubledBoxOriginToInnerEndpointSource n w ∆
          ({FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w} :
            Finset (FK.boxVerts 3 (2 * n))) =
        doubledBoxOriginToInnerEndpointSource n v := by
    simpa [doubledBoxInnerPairSource] using
      doubledBoxOriginToInnerEndpointSource_symmDiff_innerPair_eq_left
        (n := n) (v := v) (w := w) hov how hvw
  exact
    edgeCopySourceSector_card_le_containing_incrementInserted_card_of_edgeIncrementEndpointPair
      (FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxOriginToInnerEndpointSource n v)
      m e0 hedge hAB

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_of_predecessorSourceSector_card_pos
    {n : ℕ} {v w : FK.boxVerts 3 n}
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hpos :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card) :
    0 <
      (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
  lt_of_lt_of_le hpos
    (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_le_of_predecessorSourceSector_card
      (n := n) (v := v) (w := w) m e0 hedge hov how hvw)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_nonempty_of_predecessorSourceSector_nonempty
    {n : ℕ} {v w : FK.boxVerts 3 n}
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
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
    (hsource :
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) :
    (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))
      (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty := by
  have hsource_card :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card :=
    Finset.Nonempty.card_pos hsource
  have hcont_card :
      0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
    doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_of_predecessorSourceSector_card_pos
      (n := n) (v := v) (w := w) m e0 hedge hov how hvw hsource_card
  exact Finset.card_pos.mp hcont_card

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_selectedEdgeCopyPairsInCurrent_nonempty_of_predecessorSourceSector_nonempty_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hsource :
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
      (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1)) e0).Nonempty := by
  have hsource_card :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card :=
    Finset.Nonempty.card_pos hsource
  have hcont_card :
      0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
    doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_of_predecessorSourceSector_card_pos
      (n := n) (v := v) (w := w) m e0 hedge hov how hvw hsource_card
  have hin_card :
      0 <
        (edgeCopySourceSectorSelectedEdgeCopyPairsInCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card :=
    (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_selectedEdgeCopyPairsInCurrent_card_pos_of_update_zero
      (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hcont_card
  exact Finset.card_pos.mp hin_card

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_card_eq_zero_and_outsideCurrent_exhausts_of_containing_incrementInserted_card_not_pos_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hnot :
      ¬ 0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card = 0 ∧
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  constructor
  · have hsource_not :
        ¬ 0 <
          (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m).card := by
      intro hpos
      exact hnot
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_of_predecessorSourceSector_card_pos
          (n := n) (v := v) (w := w) m e0 hedge hov how hvw hpos)
    omega
  · rcases
      doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_or_outsideCurrent_exhausts_selectedEdgeCopyPairs_of_update_zero
        (n := n) (v := v) (e0 := e0) (m := m) hmzero with hpos | hexhaust
    · exact False.elim (hnot hpos)
    · exact hexhaust

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_not_nonempty_and_outsideCurrent_exhausts_of_containing_incrementInserted_not_nonempty_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hnot :
      ¬ (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))
        (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) :
    (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card := by
  have hnot_card :
      ¬ 0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card := by
    intro hpos
    exact hnot (Finset.card_pos.mp hpos)
  rcases
      doubledBoxOriginToInnerEndpoint_predecessorSourceSector_card_eq_zero_and_outsideCurrent_exhausts_of_containing_incrementInserted_card_not_pos_update_zero
        (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw hnot_card with
    ⟨hsource_zero, hexhaust⟩
  constructor
  · intro hsource
    have hsource_pos :
        0 <
          (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n w) m).card :=
      Finset.Nonempty.card_pos hsource
    omega
  · exact hexhaust

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_not_pos_iff_predecessorSourceSector_card_eq_zero_and_outsideCurrent_exhausts_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (¬ 0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card) ↔
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card = 0 ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
  constructor
  · intro hnot
    exact
      doubledBoxOriginToInnerEndpoint_predecessorSourceSector_card_eq_zero_and_outsideCurrent_exhausts_of_containing_incrementInserted_card_not_pos_update_zero
        (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw hnot
  · intro hobs hpos
    have hlt :
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card <
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
      exact
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hpos
    omega

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_containing_incrementInserted_not_nonempty_iff_predecessorSourceSector_not_nonempty_and_outsideCurrent_exhausts_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (¬ (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
      (doubledBoxOriginToInnerEndpointSource n v)
      (Function.update m e0 (m e0 + 1))
      (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).Nonempty) ↔
      (¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) ∧
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card =
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
  constructor
  · intro hnot
    exact
      doubledBoxOriginToInnerEndpoint_predecessorSourceSector_not_nonempty_and_outsideCurrent_exhausts_of_containing_incrementInserted_not_nonempty_update_zero
        (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw hnot
  · intro hobs hcont
    have hcont_card :
        0 <
          (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1))
            (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
      Finset.Nonempty.card_pos hcont
    have hlt :
        (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card <
          (edgeCopySourceSectorSelectedEdgeCopyPairs
            (FK.boxGraph 3 (2 * n))
            (doubledBoxOriginToInnerEndpointSource n v)
            (Function.update m e0 (m e0 + 1)) e0).card := by
      exact
        (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
          (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hcont_card
    omega

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_predecessorSourceSector_card_pos_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hsource :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card <
      (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card := by
  have hcont :
      0 <
        (edgeCopySourceSectorContainingCopy (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))
          (edgeCopyIncrementInserted (FK.boxGraph 3 (2 * n)) m e0)).card :=
    doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_of_predecessorSourceSector_card_pos
      (n := n) (v := v) (w := w) m e0 hedge hov how hvw hsource
  exact
    (doubledBoxOriginToInnerEndpoint_containing_incrementInserted_card_pos_iff_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_update_zero
      (n := n) (v := v) (e0 := e0) (m := m) hmzero).mp hcont

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_predecessorSourceSector_nonempty_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hsource :
      (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty) :
    (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card <
      (edgeCopySourceSectorSelectedEdgeCopyPairs
        (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1)) e0).card :=
  doubledBoxOriginToInnerEndpoint_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_predecessorSourceSector_card_pos_update_zero
    (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw
    (Finset.Nonempty.card_pos hsource)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_card_eq_zero_of_outsideCurrent_exhausts_selectedEdgeCopyPairs_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hexhaust :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card) :
    (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).card = 0 := by
  by_contra hnonzero
  have hsource :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card := by
    omega
  have hlt :=
    doubledBoxOriginToInnerEndpoint_outsideCurrent_card_lt_selectedEdgeCopyPairs_card_of_predecessorSourceSector_card_pos_update_zero
      (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw hsource
  omega

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpoint_predecessorSourceSector_not_nonempty_of_outsideCurrent_exhausts_selectedEdgeCopyPairs_update_zero
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (hmzero : m e0 = 0)
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
    (hexhaust :
      (edgeCopySourceSectorSelectedEdgeCopyPairsOutsideCurrent
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card =
        (edgeCopySourceSectorSelectedEdgeCopyPairs
          (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1)) e0).card) :
    ¬ (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w) m).Nonempty := by
  intro hsource
  have hzero :=
    doubledBoxOriginToInnerEndpoint_predecessorSourceSector_card_eq_zero_of_outsideCurrent_exhausts_selectedEdgeCopyPairs_update_zero
      (n := n) (v := v) (w := w) m e0 hmzero hedge hov how hvw hexhaust
  have hpos :
      0 <
        (edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w) m).card :=
    Finset.Nonempty.card_pos hsource
  omega


theorem boxVertTransverseHeight3_eq_zero_of_doubled_origin_eq_incl
    {n : ℕ} {v : FK.boxVerts 3 n}
    (h :
      IsingFK.boxOrigin 3 (2 * n) =
        FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :
    boxVertTransverseHeight3 v = 0 := by
  unfold boxVertTransverseHeight3
  have hsite :
      (Percolation.origin 3 : Lattice.Site 3) = (v : Lattice.Site 3) := by
    simpa [IsingFK.boxOrigin, FK.boxVertInclLE] using congrArg Subtype.val h
  have h1 := congrFun hsite (1 : Fin 3)
  have h2 := congrFun hsite (2 : Fin 3)
  simp [Percolation.origin] at h1 h2 ⊢
  simp [← h1, ← h2]


theorem boxVertTransverseHeight3_eq_zero_of_radius_zero
    {v : FK.boxVerts 3 0} :
    boxVertTransverseHeight3 v = 0 := by
  unfold boxVertTransverseHeight3
  have h1 : ((v : Lattice.Site 3) (1 : Fin 3)).natAbs = 0 := by
    have h := v.property (1 : Fin 3)
    omega
  have h2 : ((v : Lattice.Site 3) (2 : Fin 3)).natAbs = 0 := by
    have h := v.property (2 : Fin 3)
    omega
  omega

end Exact3D
end StatMech
