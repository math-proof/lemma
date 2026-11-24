module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def finiteCenteredRadialGridInterpolant
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) : Complex -> Complex :=
  fun z => finiteRadialGridInterpolant (2 * n) mesh value
    (z + (mesh * n : Real))

end
end StatMech.Universality
