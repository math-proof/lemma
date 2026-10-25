/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen.Part2


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def faceMarkedEndpointCode
    (n radius : Nat) (z : Option (FKIsingSquareFullFaceNode n))
    (hz : faceMarkedEndpointLayer n radius z) :
    Bool × Fin (radius + 1) × Fin (radius + 1) := by
  cases z with
  | none => exact False.elim hz
  | some c =>
      by_cases hlower : c.1.1 + c.2.1 <= radius
      · exact (false, ⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩)
      · have hupper :=
          (faceMarkedEndpointLayer_coordinate_cases n radius c hz).resolve_left
            hlower
        exact (true, ⟨c.1.1, by omega⟩,
          ⟨2 * n - 1 - c.2.1, by omega⟩)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
