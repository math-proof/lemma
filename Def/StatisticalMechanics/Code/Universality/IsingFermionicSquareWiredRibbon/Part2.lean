/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredCompletedIncidenceEquiv (n : Nat) :
    Equiv.Perm (FKIsingSquareWiredCarrier n) where
  toFun
    | .dart d => .bond d
    | .bond d => .dart d
    | .source => .terminal
    | .terminal => .source
  invFun
    | .dart d => .bond d
    | .bond d => .dart d
    | .source => .terminal
    | .terminal => .source
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl


def fkIsingSquareWiredTransitionEquiv
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Equiv.Perm (FKIsingSquareWiredCarrier n) where
  toFun := fkIsingSquareWiredTransitionMate n hn omega
  invFun := fkIsingSquareWiredTransitionMate n hn omega
  left_inv := fkIsingSquareWiredTransitionMate_involutive n hn omega
  right_inv := fkIsingSquareWiredTransitionMate_involutive n hn omega

end
end StatMech.Universality
