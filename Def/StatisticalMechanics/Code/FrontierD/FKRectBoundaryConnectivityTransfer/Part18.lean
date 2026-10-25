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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part15
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundaryLayerWeight {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Real :=
  Real.sqrt q ^ fkRectBoundaryLayerOpenCount eta *
    q ^ fkRectBoundaryLayerClosedCount hW evenRow state eta


def fkRectBoundaryRunState {W : Nat} (hW : 0 < W) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> FKRectBoundaryState W
  | state, [] => state
  | state, layer :: layers =>
      fkRectBoundaryRunState hW
        (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers


def fkRectBoundaryRunClosedCount {W : Nat} (hW : 0 < W) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> Nat
  | _, [] => 0
  | state, layer :: layers =>
      fkRectBoundaryLayerClosedCount hW layer.1 state layer.2 +
        fkRectBoundaryRunClosedCount hW
          (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers


def fkRectBoundaryRunOpenCount {W : Nat} :
    List (Bool × (Bool × Fin W -> Bool)) -> Nat
  | [] => 0
  | layer :: layers =>
      fkRectBoundaryLayerOpenCount layer.2 +
        fkRectBoundaryRunOpenCount layers


def fkRectBoundaryRunWeight {W : Nat} (hW : 0 < W) (q : Real) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> Real
  | _, [] => 1
  | state, layer :: layers =>
      fkRectBoundaryLayerWeight hW q layer.1 state layer.2 *
        fkRectBoundaryRunWeight hW q
          (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers

end
end StatMech.FrontierD
