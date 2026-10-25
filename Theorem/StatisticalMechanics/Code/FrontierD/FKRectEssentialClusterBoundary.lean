/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialClusterBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectClusterBoundaryDarts_iff
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (d : FKMedialDart R.medialTorus) :
    d ∈ fkRectClusterBoundaryDarts R omega x ↔
      (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R d) := by
  simp [fkRectClusterBoundaryDarts]


theorem fkRectClusterBoundaryDarts_nonempty
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    (fkRectClusterBoundaryDarts R omega x).Nonempty := by
  refine ⟨fkRectMedialDartAtPrimalVertex R x, ?_⟩
  rw [mem_fkRectClusterBoundaryDarts_iff,
    fkRectMedialDartPrimalLabel_dartAtPrimalVertex]


theorem fkRectClusterBoundaryDarts_boundaryStep_mem
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    {d : FKMedialDart R.medialTorus}
    (hd : d ∈ fkRectClusterBoundaryDarts R omega x) :
    fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d ∈
      fkRectClusterBoundaryDarts R omega x := by
  rw [mem_fkRectClusterBoundaryDarts_iff] at hd ⊢
  exact hd.trans ⟨fkRectMedialBoundaryPrimalStepWalk R omega d⟩


end
end StatMech.FrontierD
