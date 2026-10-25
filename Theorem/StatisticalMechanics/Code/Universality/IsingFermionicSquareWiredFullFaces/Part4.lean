/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

@[simp] theorem fkIsingSquareInteriorCellBlack_faceKey
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareWiredBlackFaceKey n (fkIsingSquareInteriorCellBlack n c) =
      some (fkIsingSquareInteriorCellKey n c) := by
  simp [fkIsingSquareInteriorCellBlack, fkIsingSquareInteriorCellDart,
    fkIsingSquareWiredBlackFaceKey, fkIsingSquareWedgeFaceKey,
    fkIsingSquareInteriorCellKey, fkIsingSquareInteriorCellVertex]

theorem fkIsingSquareInteriorCellKey_interior
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareInteriorFaceKey n (fkIsingSquareInteriorCellKey n c) := by
  rcases c with ⟨i, j⟩
  simp [fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey]
  constructor
  · have hi : (i.val : Int) < 2 * (n : Int) := by
      exact_mod_cast i.isLt
    omega
  · have hj : (j.val : Int) < 2 * (n : Int) := by
      exact_mod_cast j.isLt
    omega

theorem fkIsingSquareInteriorCellKey_injective (n : Nat) :
    Function.Injective (fkIsingSquareInteriorCellKey n) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrArg Prod.fst h
    simp [fkIsingSquareInteriorCellKey] at h0
    omega
  · apply Fin.ext
    have h1 := congrArg Prod.snd h
    simp [fkIsingSquareInteriorCellKey] at h1
    omega

end
end StatMech.Universality
