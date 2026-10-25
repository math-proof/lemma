/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part16


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredPhysicalTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Int :=
  fkIsingSquareWiredRawTurnCount n hn omega z -
    fkIsingSquareWiredRawTurnCount n hn omega .terminal

def fkIsingSquareWiredLiftedWinding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) : Real :=
  (fkIsingSquareWiredPhysicalTurnCount n hn omega z : Real) *
    (Real.pi / 4)

end
end StatMech.Universality
