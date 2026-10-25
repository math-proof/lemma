/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part10


namespace StatMech.Universality

open HexWalk


theorem hlha_suffixAugment_eq_forwardAugment (ts : List ℤ) :
    hlha_suffixAugment ts =
      hlha_forwardAugment (hlha_cutState ts).dir
        (ts.drop (hexW2_cutPos 0 ts)) := by
  unfold hlha_suffixAugment hlha_forwardAugment
  generalize ts.drop (hexW2_cutPos 0 ts) = suffix
  cases suffix <;> rfl


theorem hlha_sourceTurn_eq_of_cutTurn_eq (incoming : HexReturnCoord)
    {t u : ℤ} (hi : incoming.IsUnit)
    (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1)
    (hdt : HLHAAwayDir (incoming.turn t))
    (hdu : HLHAAwayDir (incoming.turn u))
    (heq : hlha_cutTurn (incoming.turn t) =
      hlha_cutTurn (incoming.turn u)) : t = u := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl <;> rcases hu with rfl | rfl <;>
    simp [HLHAAwayDir, hlha_cutTurn, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at hdt hdu heq ⊢

theorem hlha_forwardAugment_injective_of_away (incoming : HexReturnCoord)
    (hi : incoming.IsUnit) {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxaway : ∀ t us, xs = t :: us → HLHAAwayDir (incoming.turn t))
    (hyaway : ∀ t us, ys = t :: us → HLHAAwayDir (incoming.turn t))
    (heq : hlha_forwardAugment incoming xs =
      hlha_forwardAugment incoming ys) : xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlha_forwardAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlha_forwardAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hdx := hxaway x xs rfl
          have hdy := hyaway y ys rfl
          change hlha_augmentSide (incoming.turn x) xs =
            hlha_augmentSide (incoming.turn y) ys at heq
          have hcut : hlha_cutTurn (incoming.turn x) =
              hlha_cutTurn (incoming.turn y) := by
            have hget := congrArg (fun l : List ℤ => l[1]?) heq
            simpa [hlha_augmentSide] using hget
          have hxy := hlha_sourceTurn_eq_of_cutTurn_eq incoming hi hx hy
            hdx hdy hcut
          subst y
          have htail := hlha_augmentSide_injective_fixed
            (incoming.turn x) heq
          rw [htail]


end StatMech.Universality
