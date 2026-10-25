/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part5


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingFermionicBoundaryVertexNormSqFactor_pos :
    0 < isingFermionicBoundaryVertexNormSqFactor := by
  unfold isingFermionicBoundaryVertexNormSqFactor
  positivity


theorem isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor :
    Real.sqrt 2 / 2 * isingFermionicBoundaryVertexNormSqFactor =
      isingFermionicGhostCoefficient := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
  unfold isingFermionicBoundaryVertexNormSqFactor
  unfold isingFermionicGhostCoefficient
  field_simp
  nlinarith


end
end StatMech.Universality
