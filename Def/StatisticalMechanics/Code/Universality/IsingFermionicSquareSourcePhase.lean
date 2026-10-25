/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSourcePhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSourcePhase


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def FKIsingSquareDiscardedLoopTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Prop :=
  let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  let T := fkIsingSquarePhysicalTurnCount n hn (setClosed e.1 omega)
  (p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ->
      T (.dart (e, .east)) - T (.dart (e, .south)) + 2 = 8 ∨
      T (.dart (e, .east)) - T (.dart (e, .south)) + 2 = -8) ∧
    (p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west)) ->
      T (.dart (e, .west)) - T (.dart (e, .north)) + 2 = 8 ∨
      T (.dart (e, .west)) - T (.dart (e, .north)) + 2 = -8)


end
end StatMech.Universality
