/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryOrderKey_lt (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    fkIsingSquareBoundaryOrderKey n i < 8 * n := by
  rcases i with ⟨side, k⟩
  have hk := k.isLt
  cases side <;> simp [fkIsingSquareBoundaryOrderKey] <;> omega

theorem fkIsingSquareBoundaryOrderKey_injective (n : Nat) :
    Function.Injective (fkIsingSquareBoundaryOrderKey n) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ h
  cases s <;> cases t <;> simp [fkIsingSquareBoundaryOrderKey] at h ⊢ <;>
    try omega


end
end StatMech.Universality
