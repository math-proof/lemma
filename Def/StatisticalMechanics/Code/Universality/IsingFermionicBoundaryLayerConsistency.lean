/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexGhostLayerBarrier
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) -> Real
  | none => 0
  | some _ => 1 / isingFermionicGhostCoefficient


noncomputable def faceGhostLayerBarrier
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) -> Real
  | none => 0
  | some _ => 1 / isingFermionicGhostCoefficient

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
