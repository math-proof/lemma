/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullBoxCoordinateOneForm_coordinatePrimitive
    (n : Nat) (hn : 0 < n) (q : Int × Int) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).coordinatePrimitive q =
      FKIsingSquareFullIntegratedPrimitive.coordinatePrimitive n hn q := by
  rfl

theorem fkIsingSquareFullBoxCoordinateOneForm_vertexPrimitive
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).vertexPrimitive x =
      FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x := by
  rfl

theorem fkIsingSquareFullBoxCoordinateOneForm_facePrimitive
    (n : Nat) (hn : 0 < n) (c : FKIsingSquareFullFaceNode n) :
    (fkIsingSquareFullBoxCoordinateOneForm n hn).facePrimitive c =
      FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c := by
  rfl

end
end StatMech.Universality
