module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def isingRadialGridCellPoint
    (mesh : Real) (i j : Nat) (x y : Real) : Complex :=
  (mesh : Complex) *
    ⟨((i : Real) + x + (j : Real) + y + 1) / 2,
      ((i : Real) + x - ((j : Real) + y)) / 2⟩

end
end StatMech.Universality
