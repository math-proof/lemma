/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part7


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def isingCenteredRadialGridCellPoint
    (mesh : Real) (n i j : Nat) (x y : Real) : Complex :=
  isingRadialGridCellPoint mesh i j x y - (mesh * n : Real)


def isingReflectedCenteredRadialGridCellPoint
    (mesh : Real) (n i j : Nat) (x y : Real) : Complex :=
  (starRingEnd Complex)
    (isingCenteredRadialGridCellPoint mesh n i j x y)


end
end StatMech.Universality
