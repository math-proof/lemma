/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part15


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredExplorationTurnSteps
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) : List Int :=
  let path := fkIsingSquareWiredExplorationOrder n hn omega
  List.zipWith (fkIsingSquareWiredTransitionTurn n hn omega)
    path path.tail

def fkIsingSquareWiredRawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Int :=
  let path := fkIsingSquareWiredExplorationOrder n hn omega
  if z ∈ path then
    ((fkIsingSquareWiredExplorationTurnSteps n hn omega).take
      (path.idxOf z)).sum
  else 0

end
end StatMech.Universality
