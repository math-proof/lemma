/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part3
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalClusterBoundaryCycleWindingSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) : Int × Int := by
  classical
  exact ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
    if fkRectBlackBoundaryCycleInPrimalCluster R omega x C then
      fkRectBlackBoundaryCycleWinding R omega C
    else 0


def fkRectPrimalClusterBoundaryWeightSum
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) : Int × Int :=
  ∑ d : FKMedialBlackDart R.medialTorus,
    if (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) then
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d
    else 0


end
end StatMech.FrontierD
