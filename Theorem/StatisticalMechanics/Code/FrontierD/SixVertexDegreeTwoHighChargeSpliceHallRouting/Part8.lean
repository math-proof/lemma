/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part11


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection

theorem decode_high_matching
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    decoded.decode (decoded.high.pairedMatching source) = some source.1 := by
  obtain ⟨branch, hbranch⟩ := decoded.high.pairedMatching_related source
  rw [← hbranch]
  exact decoded.decode_high_target source branch


end SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
end
end StatMech.FrontierD
