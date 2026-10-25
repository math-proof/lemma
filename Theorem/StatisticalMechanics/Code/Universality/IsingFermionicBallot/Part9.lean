/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part12


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_horizontalFreeBelow_lower_eq_deep_add_band
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level - 1) level) =
      Nat.card (HorizontalFreeBelow t (level - 1) (level - 2)) +
        Nat.card (HorizontalCentralBand t level) := by
  rw [← Nat.card_sum, ← Nat.card_congr
    ((Equiv.sumCongr (deepLowerEquivSubtype t level)
      (centralBandEquivSubtype t level)).trans
      (Equiv.sumCompl (fun w : HorizontalFreeBelow t (level - 1) level =>
        lineFreeEndpoint (level - 1) w.1 < level - 2)))]

theorem natCard_horizontalFreeBelow_lower_eq_hit_add_noHit
    (t : Nat) (level : Int) :
    Nat.card (HorizontalFreeBelow t (level - 1) level) =
      Nat.card (HorizontalHitBelow t (level - 1) level) +
        Nat.card (HorizontalNoHitBelow t (level - 1) level) := by
  rw [← Nat.card_sum, ← Nat.card_congr
    (horizontalFreeBelowHitNoHitEquiv t (level - 1) level)]

theorem natCard_horizontalNoHitBelow_eq_centralBand
    (t : Nat) (level : Int) :
    Nat.card (HorizontalNoHitBelow t (level - 1) level) =
      Nat.card (HorizontalCentralBand t level) := by
  have hpartition := natCard_horizontalFreeBelow_lower_eq_hit_add_noHit t level
  have hband := natCard_horizontalFreeBelow_lower_eq_deep_add_band t level
  have hreflect := natCard_horizontalHitBelow_lower_eq_upper t level
  have hupper := natCard_horizontalFreeBelow_upper_eq_hitBelow_upper t level
  have htranslate := natCard_horizontalFreeBelow_upper_eq_deepLower t level
  omega

end
end StatMech.Universality
