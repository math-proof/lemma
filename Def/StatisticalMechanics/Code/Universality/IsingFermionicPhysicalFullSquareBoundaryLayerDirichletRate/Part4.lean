/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part3


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexBarrierOffset (n : Nat) : Real :=
  (2 * (n : Real) ^ 2 + 1) / isingFermionicGhostCoefficient

def vertexExplicitPoissonBarrier
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) → Real
  | none => 0
  | some x => fkIsingSquareBoxQuadraticBarrier n x + vertexBarrierOffset n

noncomputable def vertexExplicitPoissonBarrierBound (n : Nat) : Real :=
  (n : Real) ^ 2 / 2 + vertexBarrierOffset n

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
