/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointClampedTarget


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def isingBoundaryClamp
    {V : Type*} (boundary : V -> Prop) (value : Real) (f : V -> Real) :
    V -> Real := by
  classical
  exact fun x => if boundary x then value else f x


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
