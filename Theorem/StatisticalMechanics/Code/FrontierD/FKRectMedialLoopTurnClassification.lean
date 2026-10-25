/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

theorem fkMedialBlackBoundaryPerm_iterate_val
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (n : Nat) :
    (((fkMedialBlackBoundaryPerm pairing)^[n] d).1) =
      (fkMedialBoundaryStep pairing)^[n] d.1 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply]
      rw [ih, fkMedialBlackBoundaryPerm_val_step]

theorem fkRectRefinedBoundaryCenterAfter_succ_right
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T)
    (c : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter pairing d c (n + 1) =
      fkRectRefinedBondCenter
        (fkRectRefinedBoundaryCenterAfter pairing d c n)
        (fkMedialLocalMate pairing
          ((fkMedialBoundaryStep pairing)^[n] d)).2 := by
  induction n generalizing d c with
  | zero => rfl
  | succ n ih =>
      simp only [fkRectRefinedBoundaryCenterAfter,
        Function.iterate_succ_apply]
      exact ih (fkMedialBoundaryStep pairing d)
        (fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2)

end
end StatMech.FrontierD
