/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingRadialGridCoordinate_position
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Nat) :
    isingRadialGridCoordinate mesh (isingRadialGridPosition mesh i j) =
      ((i : Real), (j : Real)) := by
  apply Prod.ext <;>
    simp [isingRadialGridCoordinate, isingRadialGridPosition, hmesh] <;>
    field_simp <;> ring


end
end StatMech.Universality
