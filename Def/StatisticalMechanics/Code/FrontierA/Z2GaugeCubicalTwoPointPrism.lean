/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalTwoPointPrism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalTwoPointPrism


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech StatMech.Ising

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]

def oddPrismPlusTwoPoint (J beta : Real) (n : Nat)
    (v w : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) : Real :=
  (∑ sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma) *
        (rectangularPrismSpin sigma v.x v.y v.z *
          rectangularPrismSpin sigma w.x w.y w.z)) /
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n

end
end StatMech.FrontierA
