/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFaceCornerCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerGreen.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def faceEndpointPolynomialBound (k : Nat) : Real :=
  (2 * (((k + 1) + 1 : Nat) : Real) ^ 2) *
    ((((k + 1 : Nat) : Real) + 1 / isingFermionicGhostCoefficient) *
      ((k + 1 : Nat) : Real) /
        ((((k + 1) ^ 5 : Nat) : Real) / 2))

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
