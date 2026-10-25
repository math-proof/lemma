/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part5
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def oddPrismReverseVerticalChain (n : Nat)
    (x y : Fin (2 * n + 1)) (k : Nat) :
    RectangularPrismSite (2 * n + 1) (2 * n + 1) n :=
  ⟨x, y, ⟨2 * n - min k (2 * n), by omega⟩⟩

def oddPrismReverseVerticalEdgeIndex (n : Nat) (j : Fin (2 * n)) :
    Fin (2 * n) :=
  ⟨2 * n - 1 - j.val, by omega⟩

end
end StatMech.FrontierA
