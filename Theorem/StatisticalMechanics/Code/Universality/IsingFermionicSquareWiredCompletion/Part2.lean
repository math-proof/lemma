/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareLeftVerticalLower_north_available
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareLeftVerticalLower n hn k) .north := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareLeftVerticalLower]
  have hk := k.isLt
  omega

theorem fkIsingSquareMarkedB_east_available (n : Nat) (hn : 0 < n) :
    fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedB n) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedB]
  omega

theorem fkIsingSquareMarkedA_east_available (n : Nat) (hn : 0 < n) :
    fkIsingSquareDirectionAvailable n (fkIsingSquareMarkedA n) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareMarkedA]
  omega

end
end StatMech.Universality
