/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part8


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decRootedAtomList_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atom : ons_DecRootedAtom L d) :
    ons_validRootedList d (ons_dartRev L d)
      (ons_decRootedAtomList atom) ∧
      2 ≤ (ons_decRootedAtomList atom).length := by
  rcases atom with ⟨n, loop, hroot, havoid⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ons_decRootedAtomList, List.ofFn_succ, hroot]
  · change (List.ofFn loop ++ [d]).getLast? = some d
    exact List.getLast?_concat
  · intro x hx
    rw [ons_decRootedAtomList, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [List.mem_ofFn] at hx
      obtain ⟨k, rfl⟩ := hx
      exact havoid k
    · simp only [List.mem_singleton] at hx
      subst x
      exact (ons_dartRev_ne L d).symm
  · simp [ons_decRootedAtomList]

theorem ons_decRootedAtomList_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decRootedAtomList :
        ons_DecRootedAtom L d → List (ons_Dart L)) := by
  rintro ⟨n, loop, hloop⟩ ⟨n', loop', hloop'⟩ hlist
  have hlength := congrArg List.length hlist
  simp only [ons_decRootedAtomList, List.length_append,
    List.length_ofFn, List.length_singleton] at hlength
  have hn : n = n' := by omega
  subst n'
  have hofFn : List.ofFn loop = List.ofFn loop' :=
    List.append_cancel_right hlist
  have hloopEq : loop = loop' := List.ofFn_injective hofFn
  subst loop'
  rfl

theorem ons_validRootedList_eq_closedFinLoop
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (w : List (ons_Dart L))
    (hw : ons_validRootedList d (ons_dartRev L d) w)
    (hlength : 2 ≤ w.length) :
    ∃ atom : ons_DecRootedAtom L d,
      ons_decRootedAtomList atom = w := by
  let pre := w.dropLast
  have hreconstruct : pre ++ [d] = w := by
    exact List.dropLast_append_getLast? d hw.2.1
  have hprefixLength : 0 < pre.length := by
    have hwne : w ≠ [] := by
      intro h
      rw [h] at hlength
      simp at hlength
    rw [show pre.length = w.length - 1 by
      exact List.length_dropLast]
    omega
  obtain ⟨x, xs, hprefix⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_iff_length_pos.mpr hprefixLength)
  have hx : x = d := by
    rw [← hreconstruct, hprefix] at hw
    simpa using hw.1
  subst x
  let loop : Fin (xs.length + 1) → ons_Dart L := (d :: xs).get
  have hroot : loop 0 = d := by simp [loop]
  have havoid : ∀ k, loop k ≠ ons_dartRev L d := by
    intro k
    apply hw.2.2 (loop k)
    rw [← hreconstruct, List.mem_append]
    left
    rw [hprefix]
    exact List.get_mem (d :: xs) k
  let atom : ons_DecRootedAtom L d :=
    ⟨xs.length, ⟨loop, hroot, havoid⟩⟩
  refine ⟨atom, ?_⟩
  change List.ofFn loop ++ [d] = w
  rw [List.ofFn_get (d :: xs), ← hprefix, hreconstruct]


end StatMech.Onsager
