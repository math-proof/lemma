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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    Function.Injective reconnection.pairedMatching :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      reconnection.PairedRelated).mp reconnection.paired_hall)).1

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.pairedMatching_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source) : reconnection.PairedRelated source
      (reconnection.pairedMatching source) :=
  (Classical.choose_spec
    ((Fintype.all_card_le_filter_rel_iff_exists_injective
      reconnection.PairedRelated).mp reconnection.paired_hall)).2 source


end
end StatMech.FrontierD
