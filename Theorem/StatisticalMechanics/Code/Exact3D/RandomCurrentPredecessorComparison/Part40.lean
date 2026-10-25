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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part38
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem mem_doubledBoxOriginIncidentSupport
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset} :
    e ∈ doubledBoxOriginIncidentSupport n m ↔
      e ∈ doubledBoxOriginIncidentEdges n ∧ m e ≠ 0 := by
  simp [doubledBoxOriginIncidentSupport]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_eq_mem_iff
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hmS : doubledBoxOriginIncidentSupport n m = S)
    {e : ↥(FK.boxGraph 3 (2 * n)).edgeFinset} :
    e ∈ S ↔ e ∈ doubledBoxOriginIncidentEdges n ∧ m e ≠ 0 := by
  rw [← hmS]
  exact mem_doubledBoxOriginIncidentSupport

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    (doubledBoxOriginIncidentSupport n m).Nonempty ↔
      doubledBoxOriginTouchesEdgeSupport n m := by
  constructor
  · rintro ⟨e, he⟩
    rcases (mem_doubledBoxOriginIncidentSupport.mp he) with ⟨heorigin, hme⟩
    exact
      (doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
        (n := n) (m := m)).2 ⟨e, heorigin, hme⟩
  · intro htouch
    rcases
        (doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
          (n := n) (m := m)).1 htouch with
      ⟨e, heorigin, hme⟩
    exact
      ⟨e, (mem_doubledBoxOriginIncidentSupport.mpr ⟨heorigin, hme⟩)⟩

set_option linter.style.longLine false in


theorem mem_doubledBoxOriginIncidentSupport_update_sub_one_of_ne
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {e del : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (he : e ∈ doubledBoxOriginIncidentSupport n m)
    (hne : e ≠ del) :
    e ∈ doubledBoxOriginIncidentSupport n
      (Function.update m del (m del - 1)) := by
  rcases (mem_doubledBoxOriginIncidentSupport.mp he) with
    ⟨heorigin, hme⟩
  exact
    mem_doubledBoxOriginIncidentSupport.mpr
      ⟨heorigin, by simpa [Function.update_of_ne hne] using hme⟩

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_update_sub_one_eq_of_not_mem_originIncidentEdges
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {del : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hdel : del ∉ doubledBoxOriginIncidentEdges n) :
    doubledBoxOriginIncidentSupport n
        (Function.update m del (m del - 1)) =
      doubledBoxOriginIncidentSupport n m := by
  ext e
  by_cases he : e ∈ doubledBoxOriginIncidentEdges n
  · have hne : e ≠ del := by
      intro heq
      exact hdel (by simpa [heq] using he)
    simp [doubledBoxOriginIncidentSupport, he, Function.update_of_ne hne]
  · simp [doubledBoxOriginIncidentSupport, he]

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_subset_originIncidentEdges
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginIncidentSupport n m ⊆ doubledBoxOriginIncidentEdges n := by
  intro e he
  exact (mem_doubledBoxOriginIncidentSupport.mp he).1

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_card_le_six
    {n : ℕ} (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :
    (doubledBoxOriginIncidentSupport n m).card ≤ 6 :=
  (Finset.card_le_card
    (doubledBoxOriginIncidentSupport_subset_originIncidentEdges
      (n := n) (m := m))).trans
    (doubledBoxOriginIncidentEdges_card_le_six n)

set_option linter.style.longLine false in


theorem doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginIncidentSupport n m ∈
      (doubledBoxOriginIncidentEdges n).powerset := by
  rw [Finset.mem_powerset]
  exact doubledBoxOriginIncidentSupport_subset_originIncidentEdges

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPattern_eq_singleton_of_card_eq_one
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n)))
    (hcard : S.card = 1) :
    ∃ ew ∈ doubledBoxOriginIncidentEdges n, S = {ew} := by
  rcases (Finset.card_eq_one.mp hcard) with ⟨ew, hS_eq⟩
  have hsubset : S ⊆ doubledBoxOriginIncidentEdges n := by
    exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  have hew : ew ∈ doubledBoxOriginIncidentEdges n := by
    exact hsubset (by simp [hS_eq])
  exact ⟨ew, hew, hS_eq⟩

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPattern_nonempty_of_mem
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n))) :
    S.Nonempty :=
  (Finset.mem_filter.mp hS).2

set_option linter.style.longLine false in


theorem
    doubledBoxNonemptyOriginIncidentSupportPattern_card_eq_one_or_one_lt_card
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n))) :
    S.card = 1 ∨ 1 < S.card := by
  have hcard_pos : 0 < S.card :=
    Finset.Nonempty.card_pos
      (doubledBoxNonemptyOriginIncidentSupportPattern_nonempty_of_mem
        (n := n) (S := S) hS)
  omega

set_option linter.style.longLine false in


theorem doubledBoxNonemptyOriginIncidentSupportPattern_card_le_six
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n))) :
    S.card ≤ 6 := by
  have hsubset : S ⊆ doubledBoxOriginIncidentEdges n :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact (Finset.card_le_card hsubset).trans
    (doubledBoxOriginIncidentEdges_card_le_six n)

set_option linter.style.longLine false in


theorem
    doubledBoxNonemptyOriginIncidentSupportPattern_multi_card_eq_two_or_three_or_four_or_five_or_six
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n)))
    (hmulti : 1 < S.card) :
    S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨ S.card = 5 ∨ S.card = 6 := by
  have hle : S.card ≤ 6 :=
    doubledBoxNonemptyOriginIncidentSupportPattern_card_le_six
      (n := n) (S := S) hS
  omega

set_option linter.style.longLine false in


theorem
    doubledBoxNonemptyOriginIncidentSupportPattern_card_eq_one_or_two_or_three_or_four_or_five_or_six
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n))) :
    S.card = 1 ∨ S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨
      S.card = 5 ∨ S.card = 6 := by
  have hpos : 0 < S.card :=
    Finset.Nonempty.card_pos
      (doubledBoxNonemptyOriginIncidentSupportPattern_nonempty_of_mem
        (n := n) (S := S) hS)
  have hle : S.card ≤ 6 :=
    doubledBoxNonemptyOriginIncidentSupportPattern_card_le_six
      (n := n) (S := S) hS
  omega

set_option linter.style.longLine false in


theorem
    doubledBoxNonemptyOriginIncidentSupportPattern_exists_distinct_originIncidentEdges_of_one_lt_card
    {n : ℕ} {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n)))
    (hmulti : 1 < S.card) :
    ∃ e₁ ∈ S, ∃ e₂ ∈ S,
      e₁ ≠ e₂ ∧
        e₁ ∈ doubledBoxOriginIncidentEdges n ∧
          e₂ ∈ doubledBoxOriginIncidentEdges n := by
  rcases (Finset.one_lt_card.mp hmulti) with
    ⟨e₁, he₁S, e₂, he₂S, hne⟩
  have hsubset : S ⊆ doubledBoxOriginIncidentEdges n :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact ⟨e₁, he₁S, e₂, he₂S, hne, hsubset he₁S, hsubset he₂S⟩

set_option linter.style.longLine false in


theorem
    doubledBoxOriginIncidentSupport_eq_multi_exists_distinct_positive_originIncidentEdges
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hS : S ∈
      Finset.filter (fun S => S.Nonempty)
        (Finset.powerset (doubledBoxOriginIncidentEdges n)))
    (hmS : doubledBoxOriginIncidentSupport n m = S)
    (hmulti : 1 < S.card) :
    ∃ e₁ ∈ doubledBoxOriginIncidentEdges n,
      ∃ e₂ ∈ doubledBoxOriginIncidentEdges n,
        e₁ ≠ e₂ ∧ m e₁ ≠ 0 ∧ m e₂ ≠ 0 := by
  rcases
      doubledBoxNonemptyOriginIncidentSupportPattern_exists_distinct_originIncidentEdges_of_one_lt_card
        (n := n) (S := S) hS hmulti with
    ⟨e₁, he₁S, e₂, he₂S, hne, he₁origin, he₂origin⟩
  have he₁support : e₁ ∈ doubledBoxOriginIncidentSupport n m := by
    simpa [hmS] using he₁S
  have he₂support : e₂ ∈ doubledBoxOriginIncidentSupport n m := by
    simpa [hmS] using he₂S
  have he₁pos : m e₁ ≠ 0 :=
    (mem_doubledBoxOriginIncidentSupport.mp he₁support).2
  have he₂pos : m e₂ ≠ 0 :=
    (mem_doubledBoxOriginIncidentSupport.mp he₂support).2
  exact ⟨e₁, he₁origin, e₂, he₂origin, hne, he₁pos, he₂pos⟩

end Exact3D
end StatMech
