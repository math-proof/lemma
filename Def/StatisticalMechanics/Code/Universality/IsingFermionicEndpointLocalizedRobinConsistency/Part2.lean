/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def vertexMarkedEndpointLayer (n radius : Nat) :
    Option (FKIsingSquareFullVertexNode n) -> Prop
  | none => False
  | some x =>
      Int.natAbs (x.1 0 + (n : Int)) +
          Int.natAbs (x.1 1 + (n : Int)) <= radius \/
        Int.natAbs (x.1 0 + (n : Int)) +
          Int.natAbs (x.1 1 - (n : Int)) <= radius


def faceMarkedEndpointLayer (n radius : Nat) :
    Option (FKIsingSquareFullFaceNode n) -> Prop
  | none => False
  | some c =>
      let p := fkIsingSquareInteriorCellKey n c
      Int.natAbs (p.1 + (n : Int)) +
          Int.natAbs (p.2 + (n : Int)) <= radius \/
        Int.natAbs (p.1 + (n : Int)) +
          Int.natAbs (p.2 - (n : Int)) <= radius


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
