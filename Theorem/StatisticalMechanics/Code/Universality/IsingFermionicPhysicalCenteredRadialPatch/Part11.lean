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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part11


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
        n hn gridScale normalizationScale) :=
  finiteCenteredRadialGridInterpolant_continuous n gridScale _

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
        n hn gridScale normalizationScale
        (isingCenteredRadialGridPosition gridScale n i.1 j.1) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * normalizationScale) : Complex) :=
  finiteCenteredRadialGridInterpolant_position n gridScale hgridScale _ i j


end
end StatMech.Universality
