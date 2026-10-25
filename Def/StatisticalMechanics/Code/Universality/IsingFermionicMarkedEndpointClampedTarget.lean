/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointClampedTarget


namespace StatMech.Universality

open Filter

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexMarkedBoundaryEndpoint (n : Nat)
    (x : FKIsingSquareFullVertexNode n) : Prop :=
  fkIsingSquareFullVertexFixedBoundary n x /\
    0 < fkIsingSquareFullVertexGhostMultiplicity n x

def faceMarkedBoundaryEndpoint (n : Nat)
    (c : FKIsingSquareFullFaceNode n) : Prop :=
  fkIsingSquareFullFaceFixedBoundary n c /\
    0 < fkIsingSquareFullFaceGhostMultiplicity n c


noncomputable def vertexMarkedEndpointClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteGhostExtension 1
    (isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun x => (Phi (embedding x)).im))


noncomputable def faceMarkedEndpointClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteGhostExtension 0
    (isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun c => (Phi (embedding c)).im))

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
