/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def boundaryVertexEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n x d) :=
  fkIsingSquareDirectionEdge n x d hd

def boundaryVertexCornerDart (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) (hd : fkIsingSquareDirectionAvailable n x d)
    (s : FKIsingMedialSide)
    (hs : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n (boundaryVertexEdge n x d hd, s))) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(boundaryVertexEdge n x d hd, s), hs⟩


end
end StatMech.Universality
