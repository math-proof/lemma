/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_prefixAugment_eq_reverseCode (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_prefixAugment ts hleg =
      hlhda_reverseCode (ts.take (hlhda_cutPos ts hleg)) := by
  unfold hlhda_prefixAugment
  split
  · rename_i hpre
    rw [hpre]
    rfl
  · rename_i t us hpre
    rw [hpre]
    unfold hlhda_reverseCode hlhda_cutState
    rw [hpre]

theorem hlhda_reverseCode_injective {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxin : xs ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir)
    (hyin : ys ≠ [] → HLHDAInwardDir
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir)
    (heq : hlhda_reverseCode xs = hlhda_reverseCode ys) : xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlhda_reverseCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlhda_reverseCode, hlhda_emptySide,
            hlhda_augmentSide_length] at hlen
      | cons y ys =>
          let rx := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (x :: xs)
          let ry := hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (y :: ys)
          have hdx := hxin (by simp)
          have hdy := hyin (by simp)
          change hlhda_augmentSide rx.dir (loopReverse xs) =
            hlhda_augmentSide ry.dir (loopReverse ys) at heq
          have hentry : hlhda_entryTurn rx.dir = hlhda_entryTurn ry.dir := by
            have hget := congrArg (fun l : List ℤ => l[2]?) heq
            simpa [hlhda_augmentSide] using hget
          have hdir : rx.dir = ry.dir :=
            hlhda_entryTurn_injective_on_inward hdx hdy hentry
          have htail : loopReverse xs = loopReverse ys := by
            have hdrop := congrArg (List.drop 3) heq
            simpa [hlhda_augmentSide] using hdrop
          have hxyTail : xs = ys := hlha_loopReverse_injective htail
          subst ys
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          let dx := HexReturnCoord.base.turn x
          let dy := HexReturnCoord.base.turn y
          have hrx := hlha_edgeVertices_loopReverse HexReturnCoord.zero dx xs
            (by intro u hu; exact hxlegal u (by simp [hu]))
          have hry := hlha_edgeVertices_loopReverse HexReturnCoord.zero dy xs
            (by intro u hu; exact hylegal u (by simp [hu]))
          have hrxState :
              hlhr_coordRun (HexReturnCoord.zero.add dx) dx xs = rx := by
            rfl
          have hryState :
              hlhr_coordRun (HexReturnCoord.zero.add dy) dy xs = ry := by
            rfl
          rw [hrxState] at hrx
          rw [hryState] at hry
          have hfinalDir : hlha_negCoord dx = hlha_negCoord dy := by
            have hrunDir := hlhda_coordRun_dir_pos_independent
              (rx.pos.add (hlha_negCoord rx.dir))
              (ry.pos.add (hlha_negCoord ry.dir))
              (hlha_negCoord rx.dir) (loopReverse xs)
            have hrxEnd :
                hlhr_coordRun (rx.pos.add (hlha_negCoord rx.dir))
                    (hlha_negCoord rx.dir) (loopReverse xs) =
                  { pos := HexReturnCoord.zero,
                    dir := hlha_negCoord dx } := by
              simpa using hrx.2
            have hryEnd :
                hlhr_coordRun (ry.pos.add (hlha_negCoord ry.dir))
                    (hlha_negCoord ry.dir) (loopReverse xs) =
                  { pos := HexReturnCoord.zero,
                    dir := hlha_negCoord dy } := by
              simpa using hry.2
            rw [← hdir] at hrunDir hryEnd
            have hxFinal := congrArg HLHRCoordRun.dir hrxEnd
            have hyFinal := congrArg HLHRCoordRun.dir hryEnd
            exact hxFinal.symm.trans (hrunDir.trans hyFinal)
          have hdxy : dx = dy := hlha_negCoord_injective hfinalDir
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp [dx, dy, HexReturnCoord.base, HexReturnCoord.turn,
              HexReturnCoord.left, HexReturnCoord.right] at hdxy ⊢

end
end StatMech.Universality
