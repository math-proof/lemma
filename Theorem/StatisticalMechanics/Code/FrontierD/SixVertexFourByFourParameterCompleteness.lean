/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourParameterCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part4


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_rowOfBits_injective :
    Function.Injective (Nat.ofBits : SixVertexRow 4 -> Nat) := by
  intro a b h
  funext x
  have hx := congrArg (fun n : Nat => n.testBit x.val) h
  simpa [Nat.testBit_ofBits_lt _ x.val x.isLt] using hx

theorem sixVertexFourByFourAudited_firstRowZero_reverse
    (firstSeam secondSeam state : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).1)
          (sixVertexFourByFourAuditedFirstStateRow state)) =
      some (sixVertexFourByFourAuditedOppositeSeam firstSeam) <->
    state = firstSeam := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> fin_cases state <;> decide

theorem sixVertexFourByFourAudited_secondRowZero_reverse
    (firstSeam secondSeam state : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).2)
          (sixVertexFourByFourAuditedSecondStateRow state)) =
      some (sixVertexFourByFourAuditedOppositeSeam secondSeam) <->
    state = secondSeam := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> fin_cases state <;> decide

theorem sixVertexFourByFourAudited_nextVerticalRow_constant
    (value : Bool) (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (fun _ => value) below = below := by
  funext x
  unfold sixVertexFourByFourNextVerticalRow
  generalize below x = b
  cases value <;> cases b <;> simp

end StatMech.FrontierD
