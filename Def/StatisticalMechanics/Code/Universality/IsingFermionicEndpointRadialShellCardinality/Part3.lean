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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def faceEndpointRadialShell
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) -> Nat
  | none => 0
  | some c => c.1.1 + min c.2.1 (2 * n - 1 - c.2.1)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
