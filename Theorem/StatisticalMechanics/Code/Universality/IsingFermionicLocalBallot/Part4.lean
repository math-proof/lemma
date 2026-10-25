/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem localHorizontalHitReflect_injective
    (t : Nat) (start level target : Int) :
    Function.Injective (localHorizontalHitReflect t start level target) := by
  intro a b h
  have hbits := congrArg
    (fun z : LocalHorizontalHitFiber t (2 * level - start) level target => z.1.1) h
  let sa := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps a.1.1)).get (Option.ne_none_iff_isSome.mp a.2)
  let sb := (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (localHorizontalSteps b.1.1)).get (Option.ne_none_iff_isSome.mp b.2)
  have hsa : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps a.1.1) = some sa :=
    (Option.some_get (Option.ne_none_iff_isSome.mp a.2)).symm
  have hsb : isingDiagonalWalkFirstHitSplit? (start, 0) level
      (localHorizontalSteps b.1.1) = some sb :=
    (Option.some_get (Option.ne_none_iff_isSome.mp b.2)).symm
  change sa.reflectPrefix.steps.map localHorizontalCode =
    sb.reflectPrefix.steps.map localHorizontalCode at hbits
  have hsaValid : sa.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsa]
    exact localHorizontalSteps_valid a.1.1
  have hsbValid : sb.Valid := by
    unfold IsingDiagonalWalkHitSplit.Valid
    rw [firstHitSplit_steps hsb]
    exact localHorizontalSteps_valid b.1.1
  have hsaVertical : ∀ d ∈ sa.steps, d.2 = 1 := by
    rw [firstHitSplit_steps hsa]
    exact localHorizontalSteps_vertical a.1.1
  have hsbVertical : ∀ d ∈ sb.steps, d.2 = 1 := by
    rw [firstHitSplit_steps hsb]
    exact localHorizontalSteps_vertical b.1.1
  have hrefSteps : sa.reflectPrefix.steps = sb.reflectPrefix.steps := by
    rw [← localHorizontalSteps_codes _ (reflectPrefix_valid sa hsaValid)
      (reflectPrefix_steps_vertical sa hsaVertical),
      ← localHorizontalSteps_codes _ (reflectPrefix_valid sb hsbValid)
      (reflectPrefix_steps_vertical sb hsbVertical)]
    exact congrArg localHorizontalSteps hbits
  have hrefSplits : sa.reflectPrefix = sb.reflectPrefix := by
    apply Option.some.inj
    rw [← firstHitSplit_eq_some sa.reflectPrefix
        (reflectPrefix_firstHit sa (firstHitSplit_firstHit hsa)),
      ← firstHitSplit_eq_some sb.reflectPrefix
        (reflectPrefix_firstHit sb (firstHitSplit_firstHit hsb)), hrefSteps]
  have hsplits : sa = sb := reflectPrefix_injective hrefSplits
  have hpaths : localHorizontalSteps a.1.1 = localHorizontalSteps b.1.1 := by
    rw [← firstHitSplit_steps hsa, ← firstHitSplit_steps hsb, hsplits]
  have horigBits := congrArg (List.map localHorizontalCode) hpaths
  rw [localHorizontalCodes_steps, localHorizontalCodes_steps] at horigBits
  exact Subtype.ext (Subtype.ext horigBits)

theorem natCard_localHorizontalHit_reflect
    (t : Nat) (start level target : Int) :
    Nat.card (LocalHorizontalHitFiber t start level target) =
      Nat.card (LocalHorizontalHitFiber t (2 * level - start) level target) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective
      (localHorizontalHitReflect t start level target)
      (localHorizontalHitReflect_injective t start level target)
  · have h := Nat.card_le_card_of_injective
      (localHorizontalHitReflect t (2 * level - start) level target)
      (localHorizontalHitReflect_injective t (2 * level - start) level target)
    simpa only [show 2 * level - (2 * level - start) = start by ring] using h

theorem localHorizontalFreeUpper_all_hit
    (t : Nat) (level target : Int) (htarget : target < level) :
    Nat.card (LocalHorizontalHitFiber t (level + 1) level target) =
      Nat.card (LocalHorizontalFreeFiber t (level + 1) target) := by
  apply le_antisymm
  · exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  · let f : LocalHorizontalFreeFiber t (level + 1) target →
        LocalHorizontalHitFiber t (level + 1) level target := fun w => ⟨w, by
      intro hnone
      rcases exists_prefix_fst_eq_of_ge_of_gt (localHorizontalSteps w.1)
        (level + 1, 0) level (localHorizontalSteps_valid w.1) (by omega) (by
          calc
            (isingDiagonalWalkEndpoint (level + 1, 0)
                (localHorizontalSteps w.1)).1 = target := by
              rw [← lineFreeEndpoint_localHorizontalSteps]
              exact w.2.2
            _ ≤ level := htarget.le) with ⟨k, hk, heq⟩
      exact (firstHitSplit_none_endpoint_fst_ne hnone k hk) heq⟩
    exact Nat.card_le_card_of_injective f (by
      intro a b h
      exact congrArg Subtype.val h)


end
end StatMech.Universality
