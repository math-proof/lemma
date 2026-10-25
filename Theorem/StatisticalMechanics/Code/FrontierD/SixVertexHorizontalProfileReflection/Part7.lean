/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexHorizontalComplementSector_involutive
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    sixVertexHorizontalComplementSector T
        (sixVertexHorizontalComplementSector T sector) = sector := by
  apply Fin.ext
  simp only [sixVertexHorizontalComplementSector]
  omega


theorem sixVertexHorizontalProfileChooseCount_reflect
    {T : EvenTorus} (sector : Fin (T.width + 1))
    (profile : SixVertexHorizontalCompletionProfile T)
    (hvalid : profile.forcedTrue.val + profile.free.val <= T.width) :
    sixVertexHorizontalProfileChooseCount sector
        (some (sixVertexReflectHorizontalCompletionProfile profile)) =
      sixVertexHorizontalProfileChooseCount
        (sixVertexHorizontalComplementSector T sector) (some profile) := by
  unfold sixVertexHorizontalProfileChooseCount
    sixVertexReflectHorizontalCompletionProfile
    sixVertexHorizontalComplementSector
  simp only [hvalid, dif_pos]
  by_cases hleft : T.width - profile.free.val -
      profile.forcedTrue.val <= sector.val
  · by_cases hright : profile.forcedTrue.val <=
        T.width - sector.val
    · rw [if_pos hleft, if_pos hright]
      apply Nat.choose_symm_of_eq_add
      omega
    · rw [if_pos hleft, if_neg hright]
      apply Nat.choose_eq_zero_of_lt
      omega
  · by_cases hright : profile.forcedTrue.val <=
        T.width - sector.val
    · rw [if_neg hleft, if_pos hright]
      symm
      apply Nat.choose_eq_zero_of_lt
      omega
    · rw [if_neg hleft, if_neg hright]


theorem sixVertexHorizontalCompletionProfile_valid_of_eq
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (profile : SixVertexHorizontalCompletionProfile T)
    (hprofile : sixVertexHorizontalCompletionProfile T horizontal =
      some profile) :
    profile.forcedTrue.val + profile.free.val <= T.width := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · have hsubset :=
      sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal
    have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
    rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
    have hallowed := Finset.card_le_univ
      (sixVertexHorizontalTrueAllowedColumns horizontal)
    rw [sixVertexHorizontalCompletionProfile, dif_pos hcompletion] at hprofile
    have hprofile' := Option.some.inj hprofile
    subst profile
    change (sixVertexHorizontalForcedTrueColumns horizontal).card +
        (sixVertexHorizontalFreeColumns horizontal).card <= T.width
    simpa [Fintype.card_fin, add_comm] using hsplit.trans_le hallowed
  · rw [sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
      at hprofile
    simp at hprofile

theorem sixVertexReflectOptionalHorizontalCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectOptionalHorizontalCompletionProfile (T := T)) := by
  intro profile
  cases profile with
  | none => rfl
  | some profile =>
      change some (sixVertexReflectHorizontalCompletionProfile
        (sixVertexReflectHorizontalCompletionProfile profile)) = some profile
      rw [sixVertexReflectHorizontalCompletionProfile_involutive]

theorem sixVertexHorizontalCompletionProfile_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalCompletionProfile T
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexReflectOptionalHorizontalCompletionProfile
        (sixVertexHorizontalCompletionProfile T horizontal) := by
  by_cases hcompletion :
      Nonempty (SixVertexVerticalCompletion T horizontal)
  · have hreflected :=
      (sixVertexVerticalCompletion_reflect_iff horizontal).2 hcompletion
    rw [sixVertexHorizontalCompletionProfile, dif_pos hreflected,
      sixVertexHorizontalCompletionProfile, dif_pos hcompletion]
    simp only [sixVertexReflectOptionalHorizontalCompletionProfile,
      Option.some.injEq]
    apply sixVertexHorizontalCompletionProfile_ext
    · apply Fin.ext
      have hvalid :
          (sixVertexHorizontalForcedTrueColumns horizontal).card +
              (sixVertexHorizontalFreeColumns horizontal).card <= T.width := by
        have hsubset :=
          sixVertexHorizontalForcedTrueColumns_subset_trueAllowed horizontal
        have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
        rw [sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns] at hsplit
        have hallowed := Finset.card_le_univ
          (sixVertexHorizontalTrueAllowedColumns horizontal)
        simpa [Fintype.card_fin, add_comm] using hsplit.trans_le hallowed
      simp only [sixVertexReflectHorizontalCompletionProfile, hvalid,
        dif_pos]
      rw [card_sixVertexHorizontalForcedTrueColumns_reflect,
        card_sixVertexHorizontalFalseForcedColumns
          (Classical.choice hcompletion)]
    · apply Fin.ext
      exact card_sixVertexHorizontalFreeColumns_reflect horizontal
  · have hreflected :
        ¬Nonempty (SixVertexVerticalCompletion T
          (sixVertexReflectHorizontalField horizontal)) := by
      exact fun h => hcompletion
        ((sixVertexVerticalCompletion_reflect_iff horizontal).1 h)
    rw [sixVertexHorizontalCompletionProfile, dif_neg hreflected,
      sixVertexHorizontalCompletionProfile, dif_neg hcompletion]
    rfl


theorem sixVertexHorizontalSectorCompletionChooseCount_reflect
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalSectorCompletionChooseCount T sector
        (sixVertexReflectHorizontalField horizontal) =
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T sector) horizontal := by
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalSectorCompletionChooseCount_eq_profile,
    sixVertexHorizontalCompletionProfile_reflect]
  cases hprofile : sixVertexHorizontalCompletionProfile T horizontal with
  | none => rfl
  | some profile =>
      exact sixVertexHorizontalProfileChooseCount_reflect sector profile
        (sixVertexHorizontalCompletionProfile_valid_of_eq
          horizontal profile hprofile)


theorem sixVertexHorizontalChooseSum_reflect
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount
          T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T left) horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T right) horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectHorizontalPair horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflect]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectHorizontalPair horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflect]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectHorizontalPair_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectHorizontalPair_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T left)
        (sixVertexReflectHorizontalField horizontal.1.1) *
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T right)
        (sixVertexReflectHorizontalField horizontal.1.2)
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalSectorCompletionChooseCount_reflect]
  rw [sixVertexHorizontalComplementSector_involutive,
    sixVertexHorizontalComplementSector_involutive]

end
end StatMech.FrontierD
