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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialClusterBoundary
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectClusterBoundaryPerm
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    Equiv.Perm {d : FKMedialDart R.medialTorus //
      d ∈ fkRectClusterBoundaryDarts R omega x} :=
  (fkMedialBoundaryStep
    (fkRectConfigurationToMedialPairing R omega)).subtypePerm fun d => by
      simp only [mem_fkRectClusterBoundaryDarts_iff]
      constructor
      · intro hnext
        exact hnext.trans
          ⟨(fkRectMedialBoundaryPrimalStepWalk R omega d).reverse⟩
      · intro hd
        exact hd.trans ⟨fkRectMedialBoundaryPrimalStepWalk R omega d⟩

end
end StatMech.FrontierD
