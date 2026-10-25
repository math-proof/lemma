/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

noncomputable def horizontalNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  fkIsingSquareFullHorizontalIncrement n hn (shiftedCoordinate n i j)

noncomputable def verticalNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  fkIsingSquareFullVerticalIncrement n hn (shiftedCoordinate n i j)

noncomputable def primitiveNat
    (n : Nat) (hn : 0 < n) (i j : Nat) : Real :=
  isingCenteredPrimitive (horizontalNat n hn) (verticalNat n hn) (2 * n) i j

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
