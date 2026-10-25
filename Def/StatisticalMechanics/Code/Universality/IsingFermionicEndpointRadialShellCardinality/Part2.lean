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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexEndpointRadialShellCode
    (n r : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : vertexEndpointRadialShell n z = r) : Fin 3 × Fin (r + 1) := by
  cases z with
  | none => exact (0, 0)
  | some x =>
      by_cases hlower : fullVertexRowIndex n x <=
          2 * n - fullVertexRowIndex n x
      · exact (1, ⟨fullVertexColumnIndex n x, by
          simp only [vertexEndpointRadialShell, min_eq_left hlower] at hz
          omega⟩)
      · exact (2, ⟨fullVertexColumnIndex n x, by
          have hupper : 2 * n - fullVertexRowIndex n x <=
              fullVertexRowIndex n x := by omega
          simp only [vertexEndpointRadialShell, min_eq_right hupper] at hz
          omega⟩)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
