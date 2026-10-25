/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPolynomialEndpointConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFaceCornerCardinality.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2


namespace StatMech.Universality

open Filter

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicPolynomialSide (k : Nat) : Nat := (k + 1) ^ 5

def isingFermionicPolynomialRadius (k : Nat) : Nat := k + 1


noncomputable def isingFermionicPolynomialMesh (k : Nat) : Real :=
  1 / (((k + 1 : Nat) : Real) ^ 3)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
