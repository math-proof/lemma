/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part3


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_firstTransition_table (state : Fin 4) (middle : Fin 16) :
    sixVertexFourByFourAuditedFirstTransition state middle =
      sixVertexFourByFourAuditedFirstTransitionTable state middle := by
  fin_cases state <;> fin_cases middle <;> decide

theorem sixVertexFourByFourAudited_secondTransition_table (state : Fin 4) (middle : Fin 16) :
    sixVertexFourByFourAuditedSecondTransition state middle =
      sixVertexFourByFourAuditedSecondTransitionTable state middle := by
  fin_cases state <;> fin_cases middle <;> decide

theorem sixVertexFourByFourAudited_firstRowZero_opposite (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).1)
          (sixVertexFourByFourAuditedFirstStateRow firstSeam)) =
      some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

theorem sixVertexFourByFourAudited_secondRowZero_opposite (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).2)
          (sixVertexFourByFourAuditedSecondStateRow secondSeam)) =
      some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

end StatMech.FrontierD
