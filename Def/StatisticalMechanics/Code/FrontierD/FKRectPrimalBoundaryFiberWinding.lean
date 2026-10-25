/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBlackBoundaryCycleInPrimalCluster
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    FKRectConfigurationBlackBoundaryCycle R omega → Prop := by
  classical
  apply Quot.lift (fun d : FKMedialBlackDart R.medialTorus =>
    (fkRectOpenGraph R omega).Reachable x
      (fkRectMedialDartPrimalLabel R d.1))
  intro d e hde
  apply propext
  have hmedial :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).Reachable d.1 e.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkRectConfigurationToMedialPairing R omega) d e).mp hde
  have hprimal := fkRectMedial_reachable_primalLabel_reachable
    R omega hmedial
  exact ⟨fun h => h.trans hprimal, fun h => h.trans hprimal.symm⟩

end
end StatMech.FrontierD
