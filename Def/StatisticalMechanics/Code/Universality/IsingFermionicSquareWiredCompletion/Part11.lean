/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part10


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredExplorationFinset
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Finset (FKIsingSquareWiredCarrier n) :=
  Finset.univ.filter fun z =>
    (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z

def fkIsingSquareWiredExplorationTrace
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    List (FKIsingSquareWiredCarrier n) :=
  (fkIsingSquareWiredExplorationFinset n hn omega).toList

end
end StatMech.Universality
