/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexGhostGraph (n : Nat) :
    SimpleGraph (Option (FKIsingSquareFullVertexNode n)) :=
  isingFiniteGhostGraph (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

noncomputable def vertexGhostConductance (n : Nat) :
    Option (FKIsingSquareFullVertexNode n) →
      Option (FKIsingSquareFullVertexNode n) → Real :=
  isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n))

def vertexDirichletBoundary
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) → Prop :=
  isingFiniteGhostBoundaryWith (fkIsingSquareFullVertexFixedBoundary n)

def vertexGhostPrimitive
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullVertexNode n) → Real :=
  isingFiniteGhostExtension 1
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive

def faceGhostGraph (n : Nat) :
    SimpleGraph (Option (FKIsingSquareFullFaceNode n)) :=
  isingFiniteGhostGraph (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

noncomputable def faceGhostConductance (n : Nat) :
    Option (FKIsingSquareFullFaceNode n) →
      Option (FKIsingSquareFullFaceNode n) → Real :=
  isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate (fkIsingSquareFullFaceGhostMultiplicity n))

def faceDirichletBoundary
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) → Prop :=
  isingFiniteGhostBoundaryWith (fkIsingSquareFullFaceFixedBoundary n)

def faceGhostPrimitive
    (n : Nat) (hn : 0 < n) :
    Option (FKIsingSquareFullFaceNode n) → Real :=
  isingFiniteGhostExtension 0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
