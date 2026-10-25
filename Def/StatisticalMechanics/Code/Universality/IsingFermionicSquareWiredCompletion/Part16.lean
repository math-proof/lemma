/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBondTurn (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  if fkIsingSquareWiredBoundaryForward n hn d f then -6
  else if fkIsingSquareWiredBoundaryReverse n hn d f then 6
  else fkIsingSquareOrientedPrincipalBondTurn n hn d f


def fkIsingSquareWiredTransitionTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) : Int :=
  match x, y with
  | .dart d, .dart f =>
      if f = FKIsingMedialDart.localMate omega d then
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredCarrierTangentCode n hn (.dart d) + 4)
          (fkIsingSquareWiredCarrierTangentCode n hn (.dart f))
      else 0
  | .bond d, .bond f => fkIsingSquareWiredBondTurn n hn d f
  | _, _ => 0

end
end StatMech.Universality
