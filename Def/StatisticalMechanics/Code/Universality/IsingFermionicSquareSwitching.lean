/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePathSplice
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
open Finset Complex


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareLocalCarrierDarts (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Fin 4 -> FKIsingSquareMedialCarrier n
  | 0 => .dart (e, .west)
  | 1 => .dart (e, .east)
  | 2 => .dart (e, .south)
  | 3 => .dart (e, .north)

end
end StatMech.Universality
