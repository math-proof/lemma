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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def centeredRadialPatchDualFullFaceOfInterior
    (n I J : Nat)
    (hwest : 0 < centeredRadialHalf I J - 1)
    (heast : centeredRadialHalf I J - 1 + 1 < 2 * n)
    (hsouth : 0 < n + I - centeredRadialHalf I J)
    (hnorth : n + I - centeredRadialHalf I J + 1 < 2 * n) :
    FKIsingSquareFullFaceNode n := by
  refine (⟨centeredRadialHalf I J - 1, by omega⟩,
    ⟨n + I - centeredRadialHalf I J, by omega⟩)


end
end StatMech.Universality
