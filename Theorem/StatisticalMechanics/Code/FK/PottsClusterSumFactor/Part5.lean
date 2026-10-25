/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part5
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem pottsClusterSumJointFactor_shift {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (g : Multiplicative (Site d))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    pottsClusterSumJointFactor boundaryColor
        (pottsClusterFactorInputShift g input) =
      pottsJointShift g (pottsClusterSumJointFactor boundaryColor input) := by
  apply Prod.ext
  · funext x
    have h := pottsClusterSumSpin_shift boundaryColor g input.1 input.2
      (g⁻¹ • x)
    simpa [pottsClusterSumJointFactor, pottsClusterFactorInputShift,
      pottsJointShift, pottsLabelShift] using h
  · rfl


end StatMech.FK
