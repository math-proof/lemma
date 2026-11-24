module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
public import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
public import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part4
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

def oddPrismPlusSpinMean (beta : Real) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) : Real :=
  expJ (oddPrismInternalEdges n) (fun _ => beta)
    (fun x => beta * oddPrismPlusField n x) (fun sigma => spin sigma v)


def oddPrismDobrushinSpinMean (beta : Real) (n : Nat)
    (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) : Real :=
  expJ (oddPrismInternalEdges n) (fun _ => beta)
    (fun x => beta * oddPrismDobrushinField n x) (fun sigma => spin sigma v)

end
end StatMech.FrontierA
