/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part6


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFirstReturnAtomsSegments_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (atoms : List (ons_DecFirstReturnAtom L d)) :
    ons_validFactorList d (ons_dartRev L d)
      (ons_decFirstReturnAtomsSegments d atoms) := by
  intro segment hsegment
  rw [ons_decFirstReturnAtomsSegments, List.mem_map] at hsegment
  obtain ⟨atom, hatom, rfl⟩ := hsegment
  exact ons_decFirstReturnAtomSegment_valid atom

theorem ons_decFirstReturnAtomsSegments_injective
    {L : ℕ} {d : ons_Dart L} :
    Function.Injective
      (ons_decFirstReturnAtomsSegments d :
        List (ons_DecFirstReturnAtom L d) →
          List (List (ons_Dart L))) := by
  exact List.map_injective_iff.mpr
    ons_decFirstReturnAtomSegment_injective

theorem ons_decFirstReturnAtomsSegments_surjective_valid
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    (segments : List (List (ons_Dart L)))
    (hsegments : ons_validFactorList d (ons_dartRev L d) segments) :
    ∃ atoms : List (ons_DecFirstReturnAtom L d),
      ons_decFirstReturnAtomsSegments d atoms = segments := by
  refine ⟨segments.map (ons_decFirstReturnSegmentAtom L d), ?_⟩
  unfold ons_decFirstReturnAtomsSegments
  rw [List.map_map]
  induction segments with
  | nil => rfl
  | cons segment segments ih =>
      simp only [List.map_cons, Function.comp_apply]
      rw [ons_decFirstReturnSegmentAtom_segment L d segment
          (hsegments segment (by simp))]
      congr 1
      apply ih
      intro s hs
      exact hsegments s (by simp [hs])


end StatMech.Onsager
