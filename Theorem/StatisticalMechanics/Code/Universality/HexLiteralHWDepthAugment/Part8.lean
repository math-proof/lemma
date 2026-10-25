/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part7


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_suffixAugment_isLegalSAW (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW := by
  unfold hlhda_suffixAugment
  split
  · exact hlhda_emptySide_isLegalSAW
  · rename_i t us hsuf
    split
    · rename_i hflat
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hd := hlhda_cutState_inward hleg hne
      obtain ⟨hnodup, hscore, havoid⟩ :=
        hlhda_inward_empty_hypotheses _ hd
      exact hlhda_augmentSide_isLegalSAW _ [] hd (by simp) hnodup
        hscore havoid
    · rename_i hnotFlat
      obtain ⟨hd, hlegal, hnodup, hscore, havoid⟩ :=
        hlhda_suffix_side_hypotheses hleg hsuf hnotFlat
      exact hlhda_augmentSide_isLegalSAW _ us hd hlegal hnodup
        hscore havoid

theorem hlhda_suffixAugment_halfSpace (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg)
      (hlhda_suffixAugment_isLegalSAW ts hleg) := by
  cases hsuf : ts.drop (hlhda_cutPos ts hleg) with
  | nil =>
    have hout : hlhda_suffixAugment ts hleg = hlhda_emptySide := by
      unfold hlhda_suffixAugment
      split <;> simp_all
    exact hlhda_halfSpace_congr hout.symm hlhda_emptySide_halfSpace
  | cons t us =>
    by_cases hflat :
        hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor
    · have hout : hlhda_suffixAugment ts hleg =
          hlhda_augmentSide (hlhda_cutState ts hleg).dir [] := by
        unfold hlhda_suffixAugment
        split <;> simp_all
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hd := hlhda_cutState_inward hleg hne
      obtain ⟨hnodup, hscore, havoid⟩ :=
        hlhda_inward_empty_hypotheses _ hd
      apply hlhda_halfSpace_congr hout.symm
      exact hlhda_augmentSide_halfSpace _ [] hd (by simp) hnodup
        hscore havoid
    · have hout : hlhda_suffixAugment ts hleg =
          hlhda_augmentSide
            (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us := by
        unfold hlhda_suffixAugment
        split <;> simp_all
      obtain ⟨hd, hlegal, hnodup, hscore, havoid⟩ :=
        hlhda_suffix_side_hypotheses hleg hsuf hflat
      apply hlhda_halfSpace_congr hout.symm
      exact hlhda_augmentSide_halfSpace _ us hd hlegal hnodup
        hscore havoid

theorem hlhda_suffixAugment_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_suffixAugment ts hleg).length =
      (ts.drop (hlhda_cutPos ts hleg)).length + 2 := by
  unfold hlhda_suffixAugment
  split
  · rename_i hsuf
    have hlen := congrArg List.length hsuf
    simp only [List.length_drop, List.length_nil] at hlen
    simp [hlen]
  · rename_i t us hsuf
    split
    · rename_i hflat
      have hne : ts ≠ [] := by intro hnil; simp [hnil] at hsuf
      have hdmem : hlhda_flatNeighbor ∈
          hlha_edgeVertices HexReturnCoord.zero
            (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us := by
        rw [← hflat]
        exact hlhda_firstDir_mem_edgeVertices _ us
      have husNil := hlhda_suffix_flat_forces_terminal hleg hne hsuf hdmem
      subst us
      have hlen := congrArg List.length hsuf
      simp only [List.length_drop, List.length_cons, List.length_nil] at hlen
      simp [hlen]
    · have hlen := congrArg List.length hsuf
      simp only [List.length_drop, List.length_cons] at hlen
      simp [hlen]

theorem hlhda_suffixAugment_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW ∧
      HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg)
        (hlhda_suffixAugment_isLegalSAW ts hleg) ∧
      (hlhda_suffixAugment ts hleg).length =
        (ts.drop (hlhda_cutPos ts hleg)).length + 2 :=
  ⟨hlhda_suffixAugment_isLegalSAW ts hleg,
    hlhda_suffixAugment_halfSpace ts hleg,
    hlhda_suffixAugment_length ts hleg⟩


theorem hlhda_entryTurn_injective_on_inward {d e : HexReturnCoord}
    (hd : HLHDAInwardDir d) (he : HLHDAInwardDir e)
    (h : hlhda_entryTurn d = hlhda_entryTurn e) : d = e := by
  rcases hd with hd | hd <;> rcases he with he | he <;>
    rw [hd, he] at h ⊢ <;>
    simp [hlhda_entryTurn, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at h ⊢

theorem hlhda_inward_ne_flat {d : HexReturnCoord} (hd : HLHDAInwardDir d) :
    d ≠ hlhda_flatNeighbor := by
  rcases hd with hd | hd <;> rw [hd] <;>
    decide

theorem hlhda_coordRun_dir_pos_independent (p q d : HexReturnCoord)
    (ts : List ℤ) :
    (hlhr_coordRun p d ts).dir = (hlhr_coordRun q d ts).dir := by
  induction ts generalizing p q d with
  | nil => rfl
  | cons t ts ih =>
      simpa [hlhr_coordRun] using
        ih (p.add (d.turn t)) (q.add (d.turn t)) (d.turn t)

end
end StatMech.Universality
