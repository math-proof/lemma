/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredSourceDart (n : Nat) (hn : 0 < n) :=
  fkIsingSquareWiredBoundaryDart n hn .bottom

def fkIsingSquareWiredTerminalDart (n : Nat) (hn : 0 < n) :=
  fkIsingSquareWiredBoundaryDart n hn .top


def fkIsingSquareWiredIncidenceMate (n : Nat) :
    FKIsingSquareWiredCarrier n → FKIsingSquareWiredCarrier n
  | .dart d => .bond d
  | .bond d => .dart d
  | .source => .source
  | .terminal => .terminal

end
end StatMech.Universality
