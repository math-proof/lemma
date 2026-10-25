/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part16


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredTransitionTurn_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredTransitionTurn n hn omega (.dart d)
        (.dart (FKIsingMedialDart.localMate omega d)) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredCarrierTangentCode n hn (.dart d) + 4)
        (fkIsingSquareWiredCarrierTangentCode n hn
          (.dart (FKIsingMedialDart.localMate omega d))) := by
  simp [fkIsingSquareWiredTransitionTurn]


theorem fkIsingSquareWiredTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases ha : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [fkIsingSquareWiredTransitionTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, FKIsingMedialDart.localMate,
      setOpen, setClosed, fkIsingSquareSignedEighthTurn,
      FKIsingSquareDirection.eighthTurn, ha]

end
end StatMech.Universality
