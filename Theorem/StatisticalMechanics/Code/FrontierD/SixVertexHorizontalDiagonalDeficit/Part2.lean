/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalDiagonalDeficit


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalProfileChooseCount_logConcave
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (profile : Option (SixVertexHorizontalCompletionProfile T)) :
    sixVertexHorizontalProfileChooseCount
          (sixVertexHorizontalLowerSector middle hpos) profile *
        sixVertexHorizontalProfileChooseCount
          (sixVertexHorizontalUpperSector middle hlt) profile <=
      sixVertexHorizontalProfileChooseCount middle profile *
        sixVertexHorizontalProfileChooseCount middle profile := by
  cases profile with
  | none => rfl
  | some profile =>
      unfold sixVertexHorizontalProfileChooseCount
        sixVertexHorizontalLowerSector sixVertexHorizontalUpperSector
      change
        (if profile.forcedTrue.val <= middle.val - 1 then
            Nat.choose profile.free.val
              (middle.val - 1 - profile.forcedTrue.val) else 0) *
          (if profile.forcedTrue.val <= middle.val + 1 then
            Nat.choose profile.free.val
              (middle.val + 1 - profile.forcedTrue.val) else 0) <=
        (if profile.forcedTrue.val <= middle.val then
            Nat.choose profile.free.val
              (middle.val - profile.forcedTrue.val) else 0) *
          (if profile.forcedTrue.val <= middle.val then
            Nat.choose profile.free.val
              (middle.val - profile.forcedTrue.val) else 0)
      by_cases hforced : profile.forcedTrue.val <= middle.val - 1
      · have hforcedMiddle : profile.forcedTrue.val <= middle.val := by omega
        have hforcedUpper : profile.forcedTrue.val <= middle.val + 1 := by omega
        rw [if_pos hforced, if_pos hforcedUpper, if_pos hforcedMiddle]
        have hk : 0 < middle.val - profile.forcedTrue.val := by omega
        have hlower : middle.val - 1 - profile.forcedTrue.val =
            (middle.val - profile.forcedTrue.val) - 1 := by omega
        have hupper : middle.val + 1 - profile.forcedTrue.val =
            (middle.val - profile.forcedTrue.val) + 1 := by omega
        rw [hlower, hupper]
        exact natChoose_logConcave_of_pos _ _ hk
      · rw [if_neg hforced]
        simp

theorem sixVertexHorizontalDiagonalProfileDeficit_eq_zero
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (profile : Option (SixVertexHorizontalCompletionProfile T)) :
    sixVertexHorizontalProfileDeficit
        (sixVertexHorizontalLowerSector middle hpos)
        (sixVertexHorizontalUpperSector middle hlt) middle middle
        (profile, profile) = 0 := by
  rw [sixVertexHorizontalProfileDeficit_eq_sub]
  unfold sixVertexHorizontalPairProfileChooseWeight
  exact Nat.sub_eq_zero_of_le
    (sixVertexHorizontalProfileChooseCount_logConcave
      middle hpos hlt profile)

theorem sixVertexHorizontalActualDeficitToken_profiles_ne
    {T : EvenTorus} {grade : Nat × Nat}
    (middle : Fin (T.width + 1))
    (hpos : 0 < middle.val) (hlt : middle.val < T.width)
    (token : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hpos)
      (sixVertexHorizontalUpperSector middle hlt) middle middle) :
    token.1.1 ≠ token.1.2 := by
  intro heq
  have hpositive : 0 < sixVertexHorizontalProfileDeficit
      (sixVertexHorizontalLowerSector middle hpos)
      (sixVertexHorizontalUpperSector middle hlt) middle middle token.1 := by
    have hindex := token.2.2.isLt
    omega
  have hpair : token.1 = (token.1.1, token.1.1) := by
    apply Prod.ext
    · rfl
    · exact heq.symm
  rw [hpair, sixVertexHorizontalDiagonalProfileDeficit_eq_zero
    middle hpos hlt token.1.1] at hpositive
  omega

end
end StatMech.FrontierD
