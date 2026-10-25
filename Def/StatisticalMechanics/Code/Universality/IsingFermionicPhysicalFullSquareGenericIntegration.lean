/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullCoordinateOneForm

noncomputable def horizontalNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  A.horizontal (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j)

noncomputable def verticalNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  A.vertical (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j)

noncomputable def primitiveNat {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) : Real :=
  isingCenteredPrimitive A.horizontalNat A.verticalNat (2 * n) i j

end FKIsingSquareFullCoordinateOneForm
end
end StatMech.Universality
