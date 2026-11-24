module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
public import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
public import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre
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

def oddPrismInternalEdges (n : Nat) :
    Finset (Sym2 (RectangularPrismSite (2 * n + 1) (2 * n + 1) n)) :=
  Finset.univ.image (oddPrismInternalEdge n)

end
end StatMech.FrontierA
