/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem noHitEndpointToLocalNoHit_injective
    (t : Nat) (level target : Int) :
    Function.Injective (noHitEndpointToLocalNoHit t level target) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z => z.1.1) h

theorem horizontalNoHitEndpoint_weight_le
    (t : Nat) (level target : Int) :
    Nat.card (IsingHorizontalNoHitEndpointFamily t level target) /
        (2 : Real) ^ t ≤
      4 / (t + 1 : Real) := by
  by_cases htarget : target < level
  · have hnohitCard : Nat.card
        (IsingHorizontalNoHitEndpointFamily t level target) ≤
      Nat.card (LocalHorizontalNoHitFiber t (level - 1) level target) :=
      Nat.card_le_card_of_injective (noHitEndpointToLocalNoHit t level target)
        (noHitEndpointToLocalNoHit_injective t level target)
    have hpartition := natCard_localHorizontalFree_eq_hit_add_noHit
      t (level - 1) level target
    have hreflect := natCard_localHorizontalHit_reflect
      t (level - 1) level target
    have hupper := localHorizontalFreeUpper_all_hit t level target htarget
    have hrefStart : 2 * level - (level - 1) = level + 1 := by ring
    rw [hrefStart, hupper] at hreflect
    have hcardDiff : Nat.card
        (LocalHorizontalNoHitFiber t (level - 1) level target) =
      Nat.card (VerticalChoicePathFamily t (level - 1) target) -
        Nat.card (VerticalChoicePathFamily t (level + 1) target) := by
      dsimp [LocalHorizontalFreeFiber] at hpartition hreflect ⊢
      omega
    have hupperLe : Nat.card (VerticalChoicePathFamily t (level + 1) target) ≤
        Nat.card (VerticalChoicePathFamily t (level - 1) target) := by
      dsimp [LocalHorizontalFreeFiber] at hpartition hreflect
      omega
    have hden : 0 < (2 : Real) ^ t := by positivity
    calc
      _ ≤ Nat.card (LocalHorizontalNoHitFiber t (level - 1) level target) /
          (2 : Real) ^ t := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact_mod_cast hnohitCard
      _ = isingLineBinomialKernel t (level - 1) target -
          isingLineBinomialKernel t (level + 1) target := by
        rw [hcardDiff, Nat.cast_sub]
        · rw [sub_div, ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div,
            ← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
        · exact hupperLe
      _ ≤ 4 / (t + 1 : Real) := by
        convert isingLineBinomialKernel_adjacentStart_sub_le
          t (level - 1) target (by omega) using 1 <;> ring
  · have hempty : IsEmpty (IsingHorizontalNoHitEndpointFamily t level target) :=
      ⟨fun w => by
        have hbelow : lineFreeEndpoint (level - 1) w.1.1 < level := by
          by_contra hn
          have hvalid := localHorizontalSteps_valid w.1.1
          have hend : level ≤ (isingDiagonalWalkEndpoint (level - 1, 0)
              (localHorizontalSteps w.1.1)).1 := by
            rw [← lineFreeEndpoint_localHorizontalSteps]
            omega
          rcases exists_prefix_fst_eq_of_lt_of_le (localHorizontalSteps w.1.1)
            (level - 1, 0) level hvalid (by omega) hend with ⟨k, hk, heq⟩
          apply w.1.2.2 k (by simpa [localHorizontalSteps, w.1.2.1] using hk)
          rw [lineFreeEndpoint_localHorizontalSteps]
          simpa [localHorizontalSteps, List.map_take] using heq
        exact htarget (by simpa [w.2] using hbelow)⟩
    letI := hempty
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    exact div_nonneg (by norm_num) (by positivity)

end
end StatMech.Universality
