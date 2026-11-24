module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexGhostLayer (n : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Prop
  | none => False
  | some x => 0 < fkIsingSquareFullVertexGhostMultiplicity n x

def faceGhostLayer (n : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Prop
  | none => False
  | some c => 0 < fkIsingSquareFullFaceGhostMultiplicity n c

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
