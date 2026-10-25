/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
open Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


theorem fkMedialBlackDartSwap_isSwap (v : T.Vertex) :
    (fkMedialBlackDartSwap v).IsSwap :=
  Equiv.Perm.swap_isSwap_iff.mpr (fkMedialBlackDart0_ne_dart1 v)

set_option maxHeartbeats 800000 in

theorem fkMedialBlackBoundaryPerm_toggle
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v) =
      fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rcases d with ⟨⟨w, side⟩, hd⟩
  by_cases hw : w = v
  · subst w
    cases hp : pairing v <;>
      cases hc : fkMedialVertexParity v <;> cases side <;>
      simp [fkMedialBlackBoundaryPerm_val, fkMedialBlackDartSwap,
        fkMedialBlackDart0, fkMedialBlackDart1, fkMedialCheckerColor,
        fkMedialSideVertical, fkMedialTogglePairingAt, fkMedialLocalMate,
        Equiv.Perm.mul_apply, hp, hc] at hd ⊢
  · have hne0 : (⟨w, side⟩ : FKMedialDart T) ≠
        (fkMedialBlackDart0 v).1 := by
      intro h
      exact hw (congrArg (fun d : FKMedialDart T => d.1) h)
    have hne1 : (⟨w, side⟩ : FKMedialDart T) ≠
        (fkMedialBlackDart1 v).1 := by
      intro h
      exact hw (congrArg (fun d : FKMedialDart T => d.1) h)
    have hne0' : (⟨⟨w, side⟩, hd⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart0 v := fun h => hne0 (congrArg Subtype.val h)
    have hne1' : (⟨⟨w, side⟩, hd⟩ : FKMedialBlackDart T) ≠
        fkMedialBlackDart1 v := fun h => hne1 (congrArg Subtype.val h)
    simp only [fkMedialBlackBoundaryPerm_val, fkMedialBlackDartSwap,
      Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne0' hne1']
    cases side <;>
      simp [fkMedialLocalMate, fkMedialTogglePairingAt, hw]


theorem fkMedialLoopCount_toggle_mod_two
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) % 2 =
      (fkMedialLoopCount T pairing + 1) % 2 := by
  rw [← permCycleCount_fkMedialBlackBoundaryPerm,
    ← permCycleCount_fkMedialBlackBoundaryPerm]
  apply StatMech.FrontierA.permCycleCount_mod_two_toggle_of_sign_neg
  rw [fkMedialBlackBoundaryPerm_toggle, map_mul,
    (fkMedialBlackDartSwap_isSwap v).sign_eq]
  norm_num

@[simp] theorem fkMedialTogglePairingAt_toggle
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing v) v =
      pairing := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [fkMedialTogglePairingAt]
  · simp [fkMedialTogglePairingAt, hw]


theorem fkMedialLoopCount_toggle_dichotomy
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) + 1 =
        fkMedialLoopCount T pairing ∨
      fkMedialLoopCount T pairing + 1 =
        fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) := by
  have hforward := fkMedialLoopCount_toggle_le_add_one T pairing v
  have hreverse := fkMedialLoopCount_toggle_le_add_one T
    (fkMedialTogglePairingAt pairing v) v
  rw [fkMedialTogglePairingAt_toggle] at hreverse
  have hparity := fkMedialLoopCount_toggle_mod_two T pairing v
  omega

end StatMech.FrontierD
