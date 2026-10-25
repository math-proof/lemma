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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part29
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


def fkRectBoundarySeamWeight {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Real :=
  Real.sqrt q ^ fkRectBoundaryLayerOpenCount eta *
    q ^ Fintype.card (fkRectBoundarySeamGraph hW state eta).ConnectedComponent


def fkRectBoundarySeamFunctional {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) : Real :=
  ∑ eta : Bool × Fin W -> Bool,
    fkRectBoundarySeamWeight hW q state eta


def fkRectConfigurationFinalBoundaryState (R : FKRectTorus)
    (omega : R.Configuration) : FKRectBoundaryState R.width :=
  fkRectBoundaryRunState R.width_pos (fkRectBoundaryInitialState R.width)
    (fkRectConfigurationNonSeamLayers R omega)


def fkRectBoundaryTransferClusterCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  fkRectBoundaryRunClosedCount R.width_pos
      (fkRectBoundaryInitialState R.width)
      (fkRectConfigurationNonSeamLayers R omega) +
    Fintype.card
      (fkRectBoundarySeamGraph R.width_pos
        (fkRectConfigurationFinalBoundaryState R omega)
        (fkRectConfigurationLayer R omega
          (fkRectBoundarySeamRow R))).ConnectedComponent


def fkRectBoundaryTransferCoefficient (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  fkRectBoundaryRunWeight R.width_pos q (fkRectBoundaryInitialState R.width)
      (fkRectConfigurationNonSeamLayers R omega) *
    fkRectBoundarySeamWeight R.width_pos q
      (fkRectConfigurationFinalBoundaryState R omega)
      (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))


end
end StatMech.FrontierD
