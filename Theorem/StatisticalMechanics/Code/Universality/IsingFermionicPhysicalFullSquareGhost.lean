/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullFaceOfKey_key
    (n : Nat) (p : Int × Int) (hp : fkIsingSquareInteriorFaceKey n p) :
    fkIsingSquareInteriorCellKey n (fkIsingSquareFullFaceOfKey n p hp) = p := by
  rcases hp with ⟨hp0, hp1, hp2, hp3⟩
  apply Prod.ext <;>
    simp [fkIsingSquareInteriorCellKey, fkIsingSquareFullFaceOfKey,
      Int.toNat_of_nonneg] <;> omega


end
end StatMech.Universality
