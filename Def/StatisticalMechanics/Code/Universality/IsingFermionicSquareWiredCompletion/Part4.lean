/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBoundaryDart (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingMedialDart (fkSquareBoxPlanar n)
  | .bottom => fkIsingSquareDirectionDart n (fkIsingSquareMarkedA n) .east
      (fkIsingSquareMarkedA_east_available n hn) .clockwise
  | .west k => fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalLower n hn k) .north
      (fkIsingSquareLeftVerticalLower_north_available n hn k) .counterclockwise
  | .north k => fkIsingSquareDirectionDart n
      (fkIsingSquareLeftVerticalUpper n hn k) .south
      (fkIsingSquareLeftVerticalUpper_south_available n hn k) .clockwise
  | .top => fkIsingSquareDirectionDart n (fkIsingSquareMarkedB n) .east
      (fkIsingSquareMarkedB_east_available n hn) .counterclockwise

end
end StatMech.Universality
