/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexEndpointPolynomialBound (k : Nat) : Real :=
  (2 * (((k + 1) + 1 : Nat) : Real) ^ 2) *
    (((k + 1 : Nat) : Real) *
      (((k + 1 : Nat) : Real) + 1 / isingFermionicGhostCoefficient) /
        ((((k + 1) ^ 5 : Nat) : Real) / 2))

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
