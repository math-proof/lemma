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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part5


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder

noncomputable def toSpliceReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (decoded : SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  high := decoded.high
  nonHighKey := decoded.nonHighKey
  nonHigh_injective := by
    intro first hfirst second hsecond heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_nonHigh_target first hfirst,
      decoded.decode_nonHigh_target second hsecond] at hdecode
    exact Option.some.inj hdecode
  high_nonHigh_disjoint := by
    intro highSource nonHighSource hnon heq
    have hdecode := congrArg decoded.decode heq
    rw [decoded.decode_high_matching highSource,
      decoded.decode_nonHigh_target nonHighSource hnon] at hdecode
    have hsource : highSource.1 = nonHighSource := Option.some.inj hdecode
    exact hnon (hsource ▸ highSource.2)

end SixVertexHorizontalDegreeTwoLoopSelectedOutputDecoder


noncomputable def sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    FKColoredFineTwoCycleUnitTransferSpliceKey
      (sixVertexLoopDecoratedPairColored source.1) :=
  FKColoredFineTwoCycleUnitTransferSpliceKey.ofRoutedKey
    cross.toFineTwoCycleRoutedKey


end
end StatMech.FrontierD
