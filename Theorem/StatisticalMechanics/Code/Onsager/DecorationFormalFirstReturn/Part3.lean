/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part3


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFirstReturnAtomSegment_valid
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (atom : ons_DecFirstReturnAtom L d) :
    ons_isFirstReturnSegment d (ons_decFirstReturnAtomSegment atom) ∧
      ∀ x ∈ ons_decFirstReturnAtomSegment atom,
        x ≠ ons_dartRev L d := by
  rcases atom with ⟨n, loop, hloop⟩
  refine ⟨ons_closedFinLoop_isFirstReturnSegment loop hloop.1 hloop.2.1, ?_⟩
  exact ons_firstReturnSegment_avoids_of_closedLoop d loop hloop.2.2

theorem ons_decFirstReturnAtomSegment_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decFirstReturnAtomSegment :
        ons_DecFirstReturnAtom L d → List (ons_Dart L)) := by
  rintro ⟨n, loop, hloop⟩ ⟨n', loop', hloop'⟩ hsegment
  have hlength := congrArg List.length hsegment
  simp only [ons_decFirstReturnAtomSegment, List.length_append,
    List.length_ofFn, List.length_singleton] at hlength
  have hn : n = n' := by omega
  subst n'
  have hofFn : List.ofFn loop = List.ofFn loop' := by
    exact List.append_cancel_right hsegment
  have hloopEq : loop = loop' := List.ofFn_injective hofFn
  subst loop'
  rfl

theorem ons_decFirstReturnAtomSegment_surjective
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L} :
    Function.Surjective
      (fun atom : ons_DecFirstReturnAtom L d ↦
        (⟨ons_decFirstReturnAtomSegment atom,
          ons_decFirstReturnAtomSegment_valid atom⟩ :
          {segment : List (ons_Dart L) //
            ons_isFirstReturnSegment d segment ∧
              ∀ x ∈ segment, x ≠ ons_dartRev L d})) := by
  rintro ⟨segment, hfirst, havoid⟩
  obtain ⟨n, loop, hroot, hreturn, hsegment⟩ :=
    ons_firstReturnSegment_eq_closedFinLoop hfirst
  have hrev : ∀ k, loop k ≠ ons_dartRev L d := by
    intro k hk
    apply havoid (loop k)
    · rw [hsegment, List.mem_append]
      exact Or.inl (List.mem_ofFn.mpr ⟨k, rfl⟩)
    · exact hk
  let atom : ons_DecFirstReturnAtom L d :=
    ⟨n, ⟨loop, hroot, hreturn, hrev⟩⟩
  refine ⟨atom, Subtype.ext ?_⟩
  exact hsegment.symm


end StatMech.Onsager
