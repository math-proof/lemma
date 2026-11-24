module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part8


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

theorem isingReflectedCenteredRadialGridCellPoint_eq
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingReflectedCenteredRadialGridCellPoint mesh n i j x y =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (x : Complex) * ((mesh : Complex) / 2 * (1 - Complex.I)) +
        (y : Complex) * ((mesh : Complex) / 2 * (1 + Complex.I)) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridCellPoint,
      isingCenteredRadialGridCellPoint,
      isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridCellPoint,
      isingRadialGridPosition, Complex.mul_re, Complex.mul_im] <;>
    ring


end
end StatMech.Universality
