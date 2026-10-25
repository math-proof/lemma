/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part9


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_suffixAugment_eq_forwardCode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_suffixAugment ts hleg =
      hlhda_forwardCode (hlhda_cutState ts hleg).dir
        (ts.drop (hlhda_cutPos ts hleg)) := by
  unfold hlhda_suffixAugment
  split
  · rename_i hsuf
    rw [hsuf]
    rfl
  · rename_i t us hsuf
    by_cases hflat :
        hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) =
          hlhda_flatNeighbor
    · rw [hsuf]
      simp [hlhda_forwardCode, hlhda_forwardEncodedDir, hflat]
    · rw [hsuf]
      simp [hlhda_forwardCode, hlhda_forwardEncodedDir, hflat]

theorem hlhda_forwardEncodedDir_injective
    (incoming : HexReturnCoord) (hin : HLHDAInwardDir incoming)
    {t u : ℤ} (ht : t = 1 ∨ t = -1) (hu : u = 1 ∨ u = -1)
    (hdt : hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
      HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hdu : hlha_negCoord (incoming.turn u) = hlhda_flatNeighbor ∨
      HLHDAInwardDir (hlha_negCoord (incoming.turn u)))
    (heq : hlhda_forwardEncodedDir incoming t =
      hlhda_forwardEncodedDir incoming u) : t = u := by
  rcases hin with hin | hin <;> rcases ht with rfl | rfl <;>
    rcases hu with rfl | rfl <;>
    simp [hlhda_forwardEncodedDir, hin, hlha_negCoord,
      hlhda_flatNeighbor, HexReturnCoord.base, HexReturnCoord.turn,
      HexReturnCoord.left, HexReturnCoord.right] at hdt hdu heq ⊢

theorem hlhda_forwardCode_injective (incoming : HexReturnCoord)
    (hin : HLHDAInwardDir incoming) {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxdir : ∀ t us, xs = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
        HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hydir : ∀ t us, ys = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨
        HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
    (hxflat : ∀ t us, xs = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
    (hyflat : ∀ t us, ys = t :: us →
      hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
    (heq : hlhda_forwardCode incoming xs = hlhda_forwardCode incoming ys) :
    xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlhda_forwardCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlhda_forwardCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hxd := hxdir x xs rfl
          have hyd := hydir y ys rfl
          change hlhda_augmentSide (hlhda_forwardEncodedDir incoming x)
              (if hlha_negCoord (incoming.turn x) = hlhda_flatNeighbor
                then [] else xs) =
            hlhda_augmentSide (hlhda_forwardEncodedDir incoming y)
              (if hlha_negCoord (incoming.turn y) = hlhda_flatNeighbor
                then [] else ys) at heq
          have hentry : hlhda_entryTurn (hlhda_forwardEncodedDir incoming x) =
              hlhda_entryTurn (hlhda_forwardEncodedDir incoming y) := by
            have hget := congrArg (fun l : List ℤ => l[2]?) heq
            simpa [hlhda_augmentSide] using hget
          have hencInX : HLHDAInwardDir
              (hlhda_forwardEncodedDir incoming x) := by
            rcases hxd with hflat | hd
            · simpa [hlhda_forwardEncodedDir, hflat] using hin
            · have hne := hlhda_inward_ne_flat hd
              simpa [hlhda_forwardEncodedDir, hne] using hd
          have hencInY : HLHDAInwardDir
              (hlhda_forwardEncodedDir incoming y) := by
            rcases hyd with hflat | hd
            · simpa [hlhda_forwardEncodedDir, hflat] using hin
            · have hne := hlhda_inward_ne_flat hd
              simpa [hlhda_forwardEncodedDir, hne] using hd
          have hencEq := hlhda_entryTurn_injective_on_inward
            hencInX hencInY hentry
          have hxy := hlhda_forwardEncodedDir_injective incoming hin hx hy
            hxd hyd hencEq
          subst y
          by_cases hflat :
              hlha_negCoord (incoming.turn x) = hlhda_flatNeighbor
          · rw [hxflat x xs rfl hflat, hyflat x ys rfl hflat]
          · have hdrop := congrArg (List.drop 3) heq
            simpa [hlhda_augmentSide, hlhda_forwardEncodedDir, hflat] using hdrop

end
end StatMech.Universality
