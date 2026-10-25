/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem exists_sixVertexLocalSwapMask_of_disagreement
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d) :
    exists mask : SixVertexLocalIncomingPattern,
      mask d = true /\
      (forall i, mask i = true -> p i ≠ q i) /\
      (sixVertexLocalSwapMask p q mask).1.Ice /\
      (sixVertexLocalSwapMask p q mask).2.Ice /\
      sixVertexLocalCTypeCount p q <=
        sixVertexLocalCTypeCount
          (sixVertexLocalSwapMask p q mask).1
          (sixVertexLocalSwapMask p q mask).2 /\
      (sixVertexLocalSwitchMaskCount mask = 2 \/
        sixVertexLocalSwitchMaskCount mask = 4) := by
  decide +revert

theorem sixVertexRectangleLocalIncomingPattern_pairSwitch
    (mask omega eta : SixVertexRectangleArrows N M)
    (v : Fin N × Fin M) :
    (sixVertexRectangleLocalIncomingPattern
        (sixVertexRectangleSwitchFirst mask omega eta) v,
      sixVertexRectangleLocalIncomingPattern
        (sixVertexRectangleSwitchSecond mask omega eta) v) =
      sixVertexLocalSwapMask
        (sixVertexRectangleLocalIncomingPattern omega v)
        (sixVertexRectangleLocalIncomingPattern eta v)
        (sixVertexRectangleLocalSwitchMask mask v) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [sixVertexRectangleLocalIncomingPattern,
      sixVertexRectangleSwitchFirst, sixVertexRectangleSwitchSecond,
      sixVertexRectangleLocalSwitchMask, sixVertexLocalSwapMask] <;>
    split <;> simp_all

theorem sixVertexLocalSwapMask_eq_swapTwo
    (p q mask : SixVertexLocalIncomingPattern) (d e : Fin 4)
    (hmask : forall i, mask i = decide (i = d \/ i = e)) :
    sixVertexLocalSwapMask p q mask = sixVertexLocalSwapTwo p q d e := by
  apply Prod.ext <;> funext i <;>
    simp [sixVertexLocalSwapMask, sixVertexLocalSwapTwo, hmask i]


theorem sixVertexRectanglePairSwitch_weight_product_le
    {c : Real} (hc : 0 <= c)
    (mask omega eta : SixVertexRectangleArrows N M)
    (hlocal : forall v,
      omega.localWeight c v * eta.localWeight c v <=
        (sixVertexRectangleSwitchFirst mask omega eta).localWeight c v *
          (sixVertexRectangleSwitchSecond mask omega eta).localWeight c v) :
    omega.weight c * eta.weight c <=
      (sixVertexRectangleSwitchFirst mask omega eta).weight c *
        (sixVertexRectangleSwitchSecond mask omega eta).weight c := by
  simp only [SixVertexRectangleArrows.weight, <- Finset.prod_mul_distrib]
  exact Finset.prod_le_prod
    (fun v _ => mul_nonneg
      (SixVertexRectangleArrows.localWeight_nonneg hc omega v)
      (SixVertexRectangleArrows.localWeight_nonneg hc eta v))
      (fun v _ => hlocal v)


end
end StatMech.FrontierD
