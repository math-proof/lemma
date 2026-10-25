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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part4


namespace StatMech.Universality

open Filter Finset Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def faceRowPoissonBarrier
    (n : Nat) (c : FKIsingSquareFullFaceNode n) : Real :=
  (c.2.1 : Real) * (2 * (n : Real) - c.2.1) / 2

def faceExplicitPoissonBarrier
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) → Real
  | none => 0
  | some c => faceRowPoissonBarrier n c

def faceExplicitPoissonBarrierBound (n : Nat) : Real :=
  (n : Real) ^ 2 / 2

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
