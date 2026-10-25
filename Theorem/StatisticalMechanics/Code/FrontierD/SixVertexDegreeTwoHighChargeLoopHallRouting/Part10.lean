/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeLoopHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeHallRouting.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_supported
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairTwoCycleFineRelated source.1.1
      (reconnection.reconnect source).1.1 := by
  by_cases hhigh : sixVertexHorizontalDegreeTwoLoopHighCharge source
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨source, hhigh⟩
    rw [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      dif_pos hhigh, ← hbranch]
    exact sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported source
      (reconnection.key source branch)
  · rw [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      dif_neg hhigh]
    exact sixVertexHorizontalDegreeTwoLoopRoutedTarget_supported source
      (reconnection.key source false)

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.reconnect := by
  intro first second heq
  by_cases hfirst : sixVertexHorizontalDegreeTwoLoopHighCharge first <;>
    by_cases hsecond : sixVertexHorizontalDegreeTwoLoopHighCharge second
  · have hsub : (⟨first, hfirst⟩ :
        SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
          hmiddle_pos hmiddle_lt grade) = ⟨second, hsecond⟩ := by
      apply reconnection.pairedMatching_injective
      simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
        hfirst, hsecond] using heq
    exact congrArg Subtype.val hsub
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨first, hfirst⟩
    have hout : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
        (reconnection.key first branch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second
        (reconnection.key second false) := by
      calc
        _ = reconnection.pairedMatching ⟨first, hfirst⟩ := hbranch
        _ = sixVertexHorizontalDegreeTwoLoopRoutedTarget second
            (reconnection.key second false) := by
          simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hfirst, hsecond] using heq
    have hs := reconnection.source_recoverable
      first branch second false hout
    exact False.elim (hsecond (hs ▸ hfirst))
  · obtain ⟨branch, hbranch⟩ :=
      reconnection.pairedMatching_related ⟨second, hsecond⟩
    have hout : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
        (reconnection.key first false) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second
        (reconnection.key second branch) := by
      calc
        _ = reconnection.reconnect first := by
          simp [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hfirst]
        _ = reconnection.reconnect second := heq
        _ = reconnection.pairedMatching ⟨second, hsecond⟩ := by
          simp [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
            hsecond]
        _ = _ := hbranch.symm
    have hs := reconnection.source_recoverable
      first false second branch hout
    exact False.elim (hfirst (hs ▸ hsecond))
  · apply reconnection.source_recoverable first false second false
    simpa [SixVertexHorizontalDegreeTwoLoopRoutedReconnection.reconnect,
      hfirst, hsecond] using heq


end
end StatMech.FrontierD
