/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part18
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryRunWeight_eq
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W)
    (layers : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunWeight hW q state layers =
      Real.sqrt q ^ fkRectBoundaryRunOpenCount layers *
        q ^ fkRectBoundaryRunClosedCount hW state layers := by
  induction layers generalizing state with
  | nil => simp [fkRectBoundaryRunWeight, fkRectBoundaryRunOpenCount,
      fkRectBoundaryRunClosedCount]
  | cons layer layers ih =>
      rw [fkRectBoundaryRunWeight, fkRectBoundaryRunOpenCount,
        fkRectBoundaryRunClosedCount, fkRectBoundaryLayerWeight, ih]
      rw [pow_add, pow_add]
      ring

theorem fkRectBoundaryRunOpenCount_eq_sum
    {W : Nat} (layers : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunOpenCount layers =
      (layers.map fun layer =>
        fkRectBoundaryLayerOpenCount layer.2).sum := by
  induction layers with
  | nil => rfl
  | cons layer layers ih =>
      simp only [fkRectBoundaryRunOpenCount, List.map_cons, List.sum_cons, ih]


end
end StatMech.FrontierD
