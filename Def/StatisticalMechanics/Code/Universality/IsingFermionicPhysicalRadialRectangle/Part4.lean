/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareInteriorRadialRectanglePlacement

variable {n : Nat} {hn : 0 < n}

noncomputable def horizontalCarrier
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ carrier (P.horizontal i j)

noncomputable def verticalCarrier
    (P : FKIsingSquareInteriorRadialRectanglePlacement n hn) :
    Nat → Nat → FKIsingSquareWiredCarrier n :=
  fun i j ↦ carrier (P.vertical i j)


end FKIsingSquareInteriorRadialRectanglePlacement
end
end StatMech.Universality
