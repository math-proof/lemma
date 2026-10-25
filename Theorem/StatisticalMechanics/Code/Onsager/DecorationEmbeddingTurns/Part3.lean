/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part3


namespace StatMech.Onsager

theorem ons_decExpandedRoot_site
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    (ons_decExpandedRoot L q).1 = ons_decEmbedVertex L d := by
  have hne : ons_decExpandedDartList L q ≠ [] := by
    rw [List.ne_nil_iff_length_pos, ons_decExpandedDartList_length]
    have hqpos : 0 < q.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hq.not_nil
    omega
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  have ha : a ∈ (ons_decExpandedDartList L q).head? := by
    rw [hat]
    simp
  have hsite := ons_decExpandedDartList_head_site L q ha
  simpa [ons_decExpandedRoot, hat] using hsite

theorem ons_decExpandedDartList_isChain_closed
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decExpandedDartList L q ++
        [ons_decExpandedRoot L q]) := by
  apply (ons_decExpandedDartList_isChain L q).append (.singleton _)
  intro a ha b hb
  have hbhead : b = ons_decExpandedRoot L q := by
    have hroot : ons_decExpandedRoot L q = b := by simpa using hb
    exact hroot.symm
  subst b
  calc
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L d :=
      ons_decExpandedDartList_last_step L q ha
    _ = (ons_decExpandedRoot L q).1 :=
      (ons_decExpandedRoot_site L q hq).symm

theorem ons_decExpandedDartList_length_pos
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    0 < (ons_decExpandedDartList L q).length := by
  rw [ons_decExpandedDartList_length]
  have hqpos : 0 < q.length :=
    SimpleGraph.Walk.not_nil_iff_lt_length.mp hq.not_nil
  omega

end StatMech.Onsager
