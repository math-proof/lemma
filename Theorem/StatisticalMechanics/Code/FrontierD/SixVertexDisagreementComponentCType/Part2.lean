/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem intCast_sixVertexUpCount_verticalRow
    {T : EvenTorus} (omega : SixVertexArrows T) :
    (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) =
      ∑ i : Fin T.width,
        ((omega.vertical (i, svFinLast T.height_pos)).toNat : Int) := by
  classical
  rw [sixVertexUpCount, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : omega.vertical (i, svFinLast T.height_pos) <;>
    simp [svTorusVerticalRows, h]


theorem intCast_upCount_switchFirst_eq_add_seamTransfer
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchFirst mask omega eta)
          (svFinLast T.height_pos)) : Int) =
      sixVertexUpCount
          (svTorusVerticalRows T omega (svFinLast T.height_pos)) +
        sixVertexTorusMaskSeamTransfer mask omega eta := by
  rw [intCast_sixVertexUpCount_verticalRow,
    intCast_sixVertexUpCount_verticalRow]
  unfold sixVertexTorusMaskSeamTransfer
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hm : mask.vertical (i, svFinLast T.height_pos) <;>
    cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexTorusSwitchFirst, hm, ho, he]


theorem intCast_upCount_switchSecond_eq_sub_seamTransfer
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusSwitchSecond mask omega eta)
          (svFinLast T.height_pos)) : Int) =
      sixVertexUpCount
          (svTorusVerticalRows T eta (svFinLast T.height_pos)) -
        sixVertexTorusMaskSeamTransfer mask omega eta := by
  rw [intCast_sixVertexUpCount_verticalRow,
    intCast_sixVertexUpCount_verticalRow]
  unfold sixVertexTorusMaskSeamTransfer
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hm : mask.vertical (i, svFinLast T.height_pos) <;>
    cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexTorusSwitchSecond, hm, ho, he]


theorem two_le_card_sixVertexPositiveSeamDisagreements
    (T : EvenTorus) (omega eta : SixVertexArrows T) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    2 <= (sixVertexPositiveSeamDisagreements T omega eta).card := by
  classical
  let A : Finset (Fin T.width) :=
    Finset.univ.filter fun i =>
      omega.vertical (i, svFinLast T.height_pos)
  let B : Finset (Fin T.width) :=
    Finset.univ.filter fun i =>
      eta.vertical (i, svFinLast T.height_pos)
  have hA : A.card = n - 1 := by
    simpa [A, sixVertexUpCount, svTorusVerticalRows] using homegaSector
  have hB : B.card = n + 1 := by
    simpa [B, sixVertexUpCount, svTorusVerticalRows] using hetaSector
  have hpos : sixVertexPositiveSeamDisagreements T omega eta = B \ A := by
    ext i
    cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
      cases he : eta.vertical (i, svFinLast T.height_pos) <;>
      simp [sixVertexPositiveSeamDisagreements, A, B, ho, he]
  have hBA := Finset.card_sdiff_add_card_inter B A
  have hAB := Finset.card_sdiff_add_card_inter A B
  rw [Finset.inter_comm A B] at hAB
  rw [hpos]
  omega


theorem exists_two_positiveSeamDisagreements
    (T : EvenTorus) (omega eta : SixVertexArrows T) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    exists i j : Fin T.width, i ≠ j /\
      i ∈ sixVertexPositiveSeamDisagreements T omega eta /\
      j ∈ sixVertexPositiveSeamDisagreements T omega eta := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (two_le_card_sixVertexPositiveSeamDisagreements
      T omega eta n homegaSector hetaSector hn)
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
  exact ⟨i, j, hij, hs (by simp), hs (by simp)⟩


end
end StatMech.FrontierD
