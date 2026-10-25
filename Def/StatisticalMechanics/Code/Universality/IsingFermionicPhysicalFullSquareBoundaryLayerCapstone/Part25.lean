/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part25


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

noncomputable def radialPatchPrimalValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
    (fkIsingSquareRadialPatchPrimalFullVertex n m hm p)


noncomputable def radialPatchDualValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) : Real :=
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
    (fkIsingSquareRadialPatchDualFullFace n m hm hm2 q)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
