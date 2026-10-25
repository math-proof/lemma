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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def fullSquareScaledCoordinateEmbedding
    (scale : Real) (q : Int × Int) : Complex :=
  scale • fkIsingSquareWiredIntPoint q

def fullSquareScaledVertexEmbedding
    (n : Nat) (scale : Real) :
    FKIsingSquareFullVertexNode n → Complex := fun x ↦
  fullSquareScaledCoordinateEmbedding scale
    (fkIsingSquareFullVertexCoordinate n x)

def fullSquareScaledFaceEmbedding
    (n : Nat) (scale : Real) :
    FKIsingSquareFullFaceNode n → Complex := fun c ↦
  fullSquareScaledCoordinateEmbedding scale
    (fkIsingSquareFullFaceCoordinate n c)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
