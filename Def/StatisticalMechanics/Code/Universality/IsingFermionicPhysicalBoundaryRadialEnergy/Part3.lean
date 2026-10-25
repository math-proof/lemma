/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryRadialPatchHorizontalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real := fun i j ↦
  let x := fkIsingSquareBoundaryLayerRadialIncrement n hn
    (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j)
  if Even (i + j) then x else -x


noncomputable def fkIsingSquareBoundaryRadialPatchVerticalSignedIncrement
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m) :
    Nat → Nat → Real := fun i j ↦
  let x := fkIsingSquareBoundaryLayerRadialIncrement n hn
    (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j)
  if Even (i + j) then x else -x

end
end StatMech.Universality
