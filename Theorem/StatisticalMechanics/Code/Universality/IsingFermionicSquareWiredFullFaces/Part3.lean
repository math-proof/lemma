module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareInteriorCellVertex_east_available
    (n : Nat) (c : FKIsingSquareInteriorCell n) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareInteriorCellVertex n c) .east := by
  simp [fkIsingSquareDirectionAvailable, fkIsingSquareInteriorCellVertex]
  have hi := c.1.isLt
  omega

end
end StatMech.Universality
