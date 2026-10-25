/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRadialShellCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicRadialResidualSummation
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def faceEndpointRadialShellCode
    (n r : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : faceEndpointRadialShell n z = r) : Fin 3 × Fin (r + 1) := by
  cases z with
  | none => exact (0, 0)
  | some c =>
      by_cases hlower : c.2.1 <= 2 * n - 1 - c.2.1
      · exact (1, ⟨c.1.1, by
          simp only [faceEndpointRadialShell, min_eq_left hlower] at hz
          omega⟩)
      · exact (2, ⟨c.1.1, by
          have hupper : 2 * n - 1 - c.2.1 <= c.2.1 := by omega
          simp only [faceEndpointRadialShell, min_eq_right hupper] at hz
          omega⟩)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
