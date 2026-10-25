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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part5
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def FKRectPrimalAdaptiveArmEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ hsource : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i),
    let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S
          (fkRectCutConfigOfFull R psi).1 → R.Vertex) rho ∈
      FKRectPrimalUnexploredRightArmEvent R S
        (fkRectCutConfigOfFull R psi).1 source}


end
end StatMech.FrontierD
