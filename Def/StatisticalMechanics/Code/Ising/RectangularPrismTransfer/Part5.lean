/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part4
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

def rectangularPrismPlusCentralSpinNumerator
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) : Real :=
  ∑ sigma : RectangularPrismConfig m n h,
    rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma)

end
end StatMech.Ising
