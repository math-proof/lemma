/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain.Part2


namespace StatMech.Universality

open Filter Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicFixedDiamondLeftSide : Set Complex :=
  {z | z.re + z.im = -2}


def isingFermionicFixedDiamondFreeSides : Set Complex :=
  {z | z.re - z.im = -2} ∪
    {z | z.re + z.im = 2} ∪ {z | z.re - z.im = 2}


def isingFermionicFixedClosedDiamond : Set Complex :=
  {z | -2 <= z.re + z.im ∧ z.re + z.im <= 2 ∧
    -2 <= z.re - z.im ∧ z.re - z.im <= 2}

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
