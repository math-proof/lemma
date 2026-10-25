/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointClampedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointClampedTarget.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def vertexBoundaryClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullVertexNode n) -> Real := by
  classical
  exact fun
    | none => 1
    | some x =>
        if fkIsingSquareFullVertexFixedBoundary n x then 0
        else (Phi (embedding x)).im


noncomputable def faceBoundaryClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullFaceNode n) -> Real := by
  classical
  exact fun
    | none => 0
    | some c =>
        if fkIsingSquareFullFaceFixedBoundary n c then 1
        else (Phi (embedding c)).im

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
