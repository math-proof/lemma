/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveValueBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

namespace FKIsingDenseIncidenceFamily

variable {N : Nat -> Nat} {hN : forall k, 0 < N k}

variable {mesh : Nat -> Real}


def discreteVertexPrimitive
    (D : FKIsingDenseIncidenceFamily N hN mesh) (j k : Nat) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm
      (N k) (hN k)).vertexPrimitive
    (fkIsingSquareInteriorRadialEndpoint (N k) (hN k)
      (D.incidence j k))


end FKIsingDenseIncidenceFamily
end
end StatMech.Universality
