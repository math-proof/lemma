/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def isingRadialGridPosition (mesh : Real) (i j : Nat) : Complex :=
  (mesh : Complex) *
    ⟨((i : Real) + (j : Real) + 1) / 2,
      ((i : Real) - (j : Real)) / 2⟩


def isingRadialGridCoordinate (mesh : Real) (z : Complex) : Real × Real :=
  (z.re / mesh + z.im / mesh - 1 / 2,
    z.re / mesh - z.im / mesh - 1 / 2)

end
end StatMech.Universality
