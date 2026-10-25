/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredSwitching
open Finset Complex


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredEulerDefect (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) : Int :=
  2 * (numClustersBC (fkSquareBoxPlanar n).G
      (fkIsingSquareWiredDobrushinDomain n hn).wiring omega : Int) +
    (StatMech.FK.openCount (fkSquareBoxPlanar n).G omega : Int) -
    (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent : Int)

end
end StatMech.Universality
