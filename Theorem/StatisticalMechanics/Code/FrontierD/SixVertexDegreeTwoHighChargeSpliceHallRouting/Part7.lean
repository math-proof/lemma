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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part9


namespace StatMech.FrontierD

noncomputable section

open Finset

namespace SixVertexHorizontalDegreeTwoLoopSpliceReconnection

theorem reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (reconnection.reconnect source).1.1 := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source
  · rw [reconnect, dif_pos hhigh]
    exact reconnection.high.pairedMatching_supported ⟨source, hhigh⟩
  · rw [reconnect, dif_neg hhigh]
    exact sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported source
      (reconnection.nonHighKey source hhigh)

theorem reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopSpliceReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoLoopHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoLoopHighCharge second
  · have hsub : (⟨first, hfirst⟩ :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade) = ⟨second, hsecond⟩ := by
      apply reconnection.high.pairedMatching_injective
      simpa [reconnect, hfirst, hsecond] using heq
    exact congrArg Subtype.val hsub
  · exfalso
    exact reconnection.high_nonHigh_disjoint ⟨first, hfirst⟩ second
      hsecond (by simpa [reconnect, hfirst, hsecond] using heq)
  · exfalso
    exact reconnection.high_nonHigh_disjoint ⟨second, hsecond⟩ first
      hfirst (by simpa [reconnect, hfirst, hsecond] using heq.symm)
  · apply reconnection.nonHigh_injective first hfirst second hsecond
    simpa [reconnect, hfirst, hsecond] using heq

end SixVertexHorizontalDegreeTwoLoopSpliceReconnection
end
end StatMech.FrontierD
