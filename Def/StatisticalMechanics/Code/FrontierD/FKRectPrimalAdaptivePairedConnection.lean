/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalAdaptivePairedConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i targetRow : Fin R.height) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ hsource : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectLeftColumn R, i),
    ∃ htarget : ¬ FKRectPrimalFullExploredVertex R S psi
      (fkRectRightColumn R, targetRow),
    let source : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectLeftColumn R, i), fun h => hsource
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    let target : FKRectPrimalUnexploredVertex R S
        (fkRectCutConfigOfFull R psi).1 :=
      ⟨(fkRectRightColumn R, targetRow), fun h => htarget
        ((fkRectPrimalFullExploredVertex_iff R S psi _).2 h)⟩
    FK.ocd_innerRestrict
        (Subtype.val : FKRectPrimalUnexploredVertex R S
          (fkRectCutConfigOfFull R psi).1 -> R.Vertex) rho ∈
      FKRectPrimalUnexploredConnectionEvent R S
        (fkRectCutConfigOfFull R psi).1 source target}


end
end StatMech.FrontierD
