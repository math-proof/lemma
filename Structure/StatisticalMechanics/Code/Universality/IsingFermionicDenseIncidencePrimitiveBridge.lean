/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveValueBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

structure FKIsingDenseIncidenceFamily
    (N : Nat -> Nat) (hN : forall k, 0 < N k) (mesh : Nat -> Real) where
  point : Nat -> Complex
  incidence : (j k : Nat) ->
    FKIsingSquareInteriorRadialIncidence (N k) (hN k)
  embedding_tendsto : forall j, Tendsto
    (fun k =>
      FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareScaledVertexEmbedding
        (N k) (mesh k)
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k)
        (incidence j k))) atTop (nhds (point j))
  dense_range : DenseRange point

end
end StatMech.Universality
