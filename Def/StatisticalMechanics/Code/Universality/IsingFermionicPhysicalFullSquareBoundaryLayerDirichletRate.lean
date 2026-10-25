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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexSampledImaginaryTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) :
    Option (FKIsingSquareFullVertexNode n) → Real
  | none => 1
  | some x => (Phi (embedding x)).im

def faceSampledImaginaryTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) :
    Option (FKIsingSquareFullFaceNode n) → Real
  | none => 0
  | some c => (Phi (embedding c)).im


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
