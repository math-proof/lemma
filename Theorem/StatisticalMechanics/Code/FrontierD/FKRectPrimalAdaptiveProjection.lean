/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectFullGraphConfiguration_cutConfigOfFull
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1 =
      (FK.ecz_closeOff (fkRectCutGraph R) rho).1 := by
  have h := (fkRectCutClosedEdgeConfigEquiv R).apply_symm_apply
    (FK.ecz_closeOff (fkRectCutGraph R) rho)
  exact congrArg Subtype.val h


theorem fkRectOpenGraph_cutConfigOfFull
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 =
      FK.openSub (fkRectCutGraph R) rho := by
  rw [← fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)]
  have hequiv :
      (fkRectCutClosedEdgeConfigEquiv R (fkRectCutConfigOfFull R rho)).1 =
        (FK.ecz_closeOff (fkRectCutGraph R) rho).1 := by
    exact congrArg Subtype.val
      ((fkRectCutClosedEdgeConfigEquiv R).apply_symm_apply
        (FK.ecz_closeOff (fkRectCutGraph R) rho))
  rw [hequiv]
  symm
  apply FK.ecz_openSub_eq_of_edges
  intro e he
  exact (FK.ecz_closeOff_apply_edge (fkRectCutGraph R) rho he).symm


end
end StatMech.FrontierD
