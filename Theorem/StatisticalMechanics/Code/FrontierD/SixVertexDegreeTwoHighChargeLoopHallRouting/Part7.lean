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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.paired_inverse_spec
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade)
    (source : {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
        T middle hmiddle_pos hmiddle_lt grade //
      reconnection.PairedRelated source target}) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1.1
        (reconnection.key source.1.1
          (reconnection.pairedInverseBranch target source)) = target :=
  Classical.choose_spec source.2


theorem SixVertexHorizontalDegreeTwoLoopRoutedReconnection.output_recovers_occurrence
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (reconnection : SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (branch) (first second : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade)
    (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first.1
        (reconnection.key first.1 branch) =
      sixVertexHorizontalDegreeTwoLoopRoutedTarget second.1
        (reconnection.key second.1 branch)) :
    sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv first =
      sixVertexHorizontalDegreeTwoLoopHighChargeOccurrenceEquiv second := by
  have hsource : first = second := by
    apply Subtype.ext
    exact reconnection.source_recoverable
      first.1 branch second.1 branch heq
  rw [hsource]


end
end StatMech.FrontierD
