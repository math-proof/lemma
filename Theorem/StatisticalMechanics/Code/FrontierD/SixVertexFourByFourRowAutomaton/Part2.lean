/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton.Part2


namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_firstStateCode_iff (row : SixVertexRow 4) :
    sixVertexUpCount row = 1 <->
      Nat.ofBits row = 1 \/ Nat.ofBits row = 2 \/
        Nat.ofBits row = 4 \/ Nat.ofBits row = 8 := by
  revert row
  decide

theorem sixVertexFourByFourAudited_secondStateCode_iff (row : SixVertexRow 4) :
    sixVertexUpCount row = 3 <->
      Nat.ofBits row = 7 \/ Nat.ofBits row = 11 \/
        Nat.ofBits row = 13 \/ Nat.ofBits row = 14 := by
  revert row
  decide

theorem sixVertexFourByFourAudited_firstStateDecode_spec (row : SixVertexRow 4) :
    match sixVertexFourByFourAuditedFirstStateDecode row with
    | some state => Nat.ofBits row = Nat.ofBits (sixVertexFourByFourAuditedFirstStateRow state)
    | none => sixVertexUpCount row ≠ 1 := by
  have hcode := sixVertexFourByFourAudited_firstStateCode_iff row
  simp only [sixVertexFourByFourAuditedFirstStateDecode]
  split_ifs with h1 h2 h3 h4 <;>
    simp_all [sixVertexFourByFourAuditedFirstStateRow,
      sixVertexFourByFourSectorOneSeamMask] <;> decide

theorem sixVertexFourByFourAudited_secondStateDecode_spec (row : SixVertexRow 4) :
    match sixVertexFourByFourAuditedSecondStateDecode row with
    | some state => Nat.ofBits row = Nat.ofBits (sixVertexFourByFourAuditedSecondStateRow state)
    | none => sixVertexUpCount row ≠ 3 := by
  have hcode := sixVertexFourByFourAudited_secondStateCode_iff row
  simp only [sixVertexFourByFourAuditedSecondStateDecode]
  split_ifs with h1 h2 h3 h4 <;>
    simp_all [sixVertexFourByFourAuditedSecondStateRow,
      sixVertexFourByFourSectorThreeSeamMask] <;> decide

end StatMech.FrontierD
