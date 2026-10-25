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
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

abbrev OddPrismInternalIndex (n : Nat) :=
  (Fin (2 * n) × Fin (2 * n + 1) × Fin (2 * n + 1)) ⊕
    ((Fin (2 * n + 1) × Fin (2 * n) × Fin (2 * n + 1)) ⊕
      (Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (2 * n)))


end
end StatMech.FrontierA
