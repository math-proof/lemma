/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkExtract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycles
import Def.StatisticalMechanics.Code.Onsager.DecorationWalkExtract.Part2


namespace StatMech.Onsager

theorem ons_decCycleFirstReturn_isFirstReturn
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hnodup : ext.Nodup := ons_decWalkExternalDarts_nodup q hq
  have hdnot : d ∉ ext.tail := by
    rw [hext, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨ext.tail.reverse, rfl, ?_⟩
  intro e he hed
  subst e
  exact hdnot (by simpa using he)

theorem ons_decCycleFirstReturn_avoids_reverse
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  have hdmem : d ∈ ext := by rw [hext]; simp
  have hrevnot : ons_dartRev L d ∉ ext := by
    intro hrev
    have hinj := List.inj_on_of_nodup_map
      (ons_decWalkExternalDarts_portEdge_nodup q hq)
    have heq : d = ons_dartRev L d :=
      hinj hdmem hrev (ons_portEdge_rev L d).symm
    exact (ons_dartRev_ne_self L d) heq.symm
  have hrevnotTail : ons_dartRev L d ∉ ext.tail := by
    intro hrev
    exact hrevnot (by rw [hext]; simp [hrev])
  intro e he
  change e ∈
    (d :: (ons_decWalkExternalDarts q).tail.reverse) ++ [d] at he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_cons.mp he with hed | he
    · subst e
      exact (ons_dartRev_ne_self L d).symm
    · intro hed
      rw [hed] at he
      exact hrevnotTail (by simpa [ext] using he)
  · have hed : e = d := by simpa using he
    subst e
    exact (ons_dartRev_ne_self L d).symm

theorem ons_decCycleFirstReturn_valid
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_isFirstReturnSegment d (ons_decCycleFirstReturn q) ∧
      ∀ e ∈ ons_decCycleFirstReturn q, e ≠ ons_dartRev L d :=
  ⟨ons_decCycleFirstReturn_isFirstReturn q hq hsnd,
    ons_decCycleFirstReturn_avoids_reverse q hq hsnd⟩

end StatMech.Onsager
