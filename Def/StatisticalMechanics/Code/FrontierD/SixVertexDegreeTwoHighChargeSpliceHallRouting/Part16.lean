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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part7


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder

noncomputable def toSelectedOutputDecoder
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := fun source hnon =>
    sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source
      (decoded.nonHighMask source hnon)
  decode := decoded.decode
  decode_high_matching := decoded.decode_high_matching
  decode_nonHigh_target := decoded.decode_nonHigh_target

noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade :=
  decoded.toSelectedOutputDecoder.toSpliceReconnection

end SixVertexHorizontalDegreeTwoLoopSelectedOutputFullMaskDecoder


noncomputable def
    SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection.toSelectedOutputDecoder
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopDecodedSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := decoded.nonHighKey
  decode := decoded.decode
  decode_high_matching := decoded.decode_high_matching
  decode_nonHigh_target := decoded.decode_nonHigh_target

def SixVertexHorizontalDegreeTwoLoopSpliceReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopSpliceReconnection
    T middle hmiddle_pos hmiddle_lt grade)

end
end StatMech.FrontierD
