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


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexEndpointRadialShell
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) -> Nat
  | none => 0
  | some x => fullVertexColumnIndex n x +
      min (fullVertexRowIndex n x)
        (2 * n - fullVertexRowIndex n x)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
