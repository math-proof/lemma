/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareWiredDiscardedLoopTurnModSixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Prop :=
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  let T := fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
  (p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) →
      T (.dart (e, .north)) - T (.dart (e, .west)) - 2 ≡ 8 [ZMOD 16]) ∧
    (p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) →
      T (.dart (e, .south)) - T (.dart (e, .east)) - 2 ≡ 8 [ZMOD 16])


end
end StatMech.Universality
