/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexReflectHorizontalPair_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectHorizontalPair (T := T)) := by
  intro horizontal
  apply Prod.ext <;> funext v
  · apply congrArg horizontal.1
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl
  · apply congrArg horizontal.2
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl

theorem sixVertexHorizontalPairBigrade_reflect
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectHorizontalPair horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade sixVertexReflectHorizontalPair
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

theorem sixVertexHorizontalColumnSeamAllowed_reflect_false_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed
        (sixVertexReflectHorizontalField horizontal) i false ↔
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) true := by
  rw [sixVertexHorizontalColumnSeamAllowed_false_iff_forward,
    sixVertexHorizontalColumnSeamAllowed_true_iff_backward]
  unfold sixVertexReflectHorizontalField
  change SixVertexForwardInterlaced
      (fun j => horizontal
        (sixVertexCyclicNeg T.width_pos
          (SixVertexArrows.cyclicPred T.width_pos i), j))
      (fun j => horizontal (sixVertexCyclicNeg T.width_pos i, j)) ↔
    SixVertexForwardInterlaced
      (fun j => horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i), j))
      (fun j => horizontal
        (SixVertexArrows.cyclicPred T.width_pos
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos i)), j))
  rw [sixVertexCyclicNeg_cyclicPred,
    svCyclicPred_finitePeriodicSucc]

theorem sixVertexHorizontalColumnSeamAllowed_reflect_true_iff
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (i : Fin T.width) :
    sixVertexHorizontalColumnSeamAllowed
        (sixVertexReflectHorizontalField horizontal) i true ↔
      sixVertexHorizontalColumnSeamAllowed horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i)) false := by
  rw [sixVertexHorizontalColumnSeamAllowed_true_iff_backward,
    sixVertexHorizontalColumnSeamAllowed_false_iff_forward]
  unfold sixVertexReflectHorizontalField
  change SixVertexForwardInterlaced
      (fun j => horizontal (sixVertexCyclicNeg T.width_pos i, j))
      (fun j => horizontal
        (sixVertexCyclicNeg T.width_pos
          (SixVertexArrows.cyclicPred T.width_pos i), j)) ↔
    SixVertexForwardInterlaced
      (fun j => horizontal
        (SixVertexArrows.cyclicPred T.width_pos
          (finitePeriodicSucc T.width_pos
            (sixVertexCyclicNeg T.width_pos i)), j))
      (fun j => horizontal
        (finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i), j))
  rw [sixVertexCyclicNeg_cyclicPred,
    svCyclicPred_finitePeriodicSucc]

end
end StatMech.FrontierD
