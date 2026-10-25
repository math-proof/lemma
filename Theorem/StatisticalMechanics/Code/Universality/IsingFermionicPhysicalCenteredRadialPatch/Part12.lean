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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale) := by
  exact
    (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous
      n hn gridScale normalizationScale).comp Complex.continuous_conj

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale
        ((starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j x y)) =
      complexBilinearCell
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 1, by omega⟩ ⟨j, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j + 1, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex)) x y := by
  unfold
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
  have hconj : (starRingEnd Complex)
      ((starRingEnd Complex)
        (isingCenteredRadialGridCellPoint gridScale n i j x y)) =
      isingCenteredRadialGridCellPoint gridScale n i j x y := by
    apply Complex.ext <;> simp
  rw [hconj]
  exact finiteCenteredRadialGridInterpolant_cellPoint
    n gridScale hgridScale _ i j hi hj x y hx0 hx1 hy0 hy1

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale
        ((starRingEnd Complex)
          (isingCenteredRadialGridPosition gridScale n i.1 j.1)) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * normalizationScale) : Complex) := by
  unfold
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
  have hconj : (starRingEnd Complex)
      ((starRingEnd Complex)
        (isingCenteredRadialGridPosition gridScale n i.1 j.1)) =
      isingCenteredRadialGridPosition gridScale n i.1 j.1 := by
    apply Complex.ext <;> simp
  rw [hconj]
  exact
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position
      n hn gridScale normalizationScale hgridScale i j

end
end StatMech.Universality
