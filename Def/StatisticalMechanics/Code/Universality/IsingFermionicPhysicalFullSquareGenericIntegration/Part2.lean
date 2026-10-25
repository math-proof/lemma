/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullCoordinateOneForm

noncomputable def coordinatePrimitive {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int) : Real :=
  A.primitiveNat
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).1
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).2

end FKIsingSquareFullCoordinateOneForm
end
end StatMech.Universality
