/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexMarkedEndpointCode
    (n radius : Nat) (z : Option (FKIsingSquareFullVertexNode n))
    (hz : vertexMarkedEndpointLayer n radius z) :
    Bool × Fin (radius + 1) × Fin (radius + 1) := by
  cases z with
  | none => exact False.elim hz
  | some x =>
      by_cases hlower : fullVertexColumnIndex n x +
          fullVertexRowIndex n x <= radius
      · exact (false, ⟨fullVertexColumnIndex n x, by omega⟩,
          ⟨fullVertexRowIndex n x, by omega⟩)
      · have hupper :=
          (vertexMarkedEndpointLayer_coordinate_cases n radius x hz).resolve_left
            hlower
        exact (true, ⟨fullVertexColumnIndex n x, by omega⟩,
          ⟨2 * n - fullVertexRowIndex n x, by omega⟩)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
