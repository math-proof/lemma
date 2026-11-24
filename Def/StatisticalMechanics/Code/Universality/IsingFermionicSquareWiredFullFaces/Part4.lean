module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part3


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

def fkIsingSquareInteriorCellDart (n : Nat)
    (c : FKIsingSquareInteriorCell n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionDart n (fkIsingSquareInteriorCellVertex n c) .east
    (fkIsingSquareInteriorCellVertex_east_available n c) .counterclockwise

def fkIsingSquareInteriorCellBlack (n : Nat)
    (c : FKIsingSquareInteriorCell n) : FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (fkIsingSquareInteriorCellDart n c), by
    simp [fkIsingSquareInteriorCellDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
      fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor]⟩

end
end StatMech.Universality
