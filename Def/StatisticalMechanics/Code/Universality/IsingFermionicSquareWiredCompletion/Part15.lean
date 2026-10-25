/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part14


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredCarrierTangentCode (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredCarrier n → Int
  | .dart d | .bond d => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n d) (fkIsingSquareSideCorner d.2).2
  | .source => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n (fkIsingSquareWiredSourceDart n hn))
      (fkIsingSquareSideCorner (fkIsingSquareWiredSourceDart n hn).2).2 + 4
  | .terminal => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n (fkIsingSquareWiredTerminalDart n hn))
      (fkIsingSquareSideCorner (fkIsingSquareWiredTerminalDart n hn).2).2


def fkIsingSquareOrientedPrincipalBondTurn (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  let raw := fkIsingSquareSignedEighthTurn
    (fkIsingSquareWiredCarrierTangentCode n hn (.bond d))
    (fkIsingSquareWiredCarrierTangentCode n hn (.bond f) + 4)
  if raw = -4 ∧ (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    then 4 else raw

def fkIsingSquareWiredBoundaryForward (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  (d = fkIsingSquareWiredSourceDart n hn ∧
      f = fkIsingSquareWiredTerminalDart n hn) ∨
    ∃ k : Fin (2 * n),
      d = fkIsingSquareWiredBoundaryDart n hn (.west k) ∧
      f = fkIsingSquareWiredBoundaryDart n hn (.north k)

def fkIsingSquareWiredBoundaryReverse (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  fkIsingSquareWiredBoundaryForward n hn f d

end
end StatMech.Universality
