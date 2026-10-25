/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectBlackBoundaryCycleInPrimalCluster_mk
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (d : FKMedialBlackDart R.medialTorus) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x (Quot.mk _ d) ↔
      (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d.1) :=
  Iff.rfl


end
end StatMech.FrontierD
