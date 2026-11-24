module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
public import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
public import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part2
open scoped BigOperators
open Finset
open MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def oddPrismPlusField (n : Nat) :
    RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real :=
  fun v => rectangularPrismBoundaryDegree v


def oddPrismDobrushinField (n : Nat) :
    RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real :=
  fun v => oddRectangularPrismDobrushinSign n v.z *
    rectangularPrismBoundaryDegree v

end
end StatMech.FrontierA
