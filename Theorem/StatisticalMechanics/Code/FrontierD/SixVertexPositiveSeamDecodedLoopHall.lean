/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection

theorem source_recoverable
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (first second : SixVertexHorizontalDegreeTwoLoopHallSource T middle
      hmiddle_pos hmiddle_lt grade) (firstBranch secondBranch : Bool)
    (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first
          (data.key first firstBranch) =
        sixVertexHorizontalDegreeTwoLoopRoutedTarget second
          (data.key second secondBranch)) :
    first = second := by
  have hdecode := congrArg data.decode heq
  rw [data.decode_target first firstBranch,
    data.decode_target second secondBranch] at hdecode
  exact hdecode


theorem high_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (data.key source.1 false) ≠
      sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
        (data.key source.1 true) := by
  intro heq
  have harrows := congrArg
    sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair heq
  apply (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source).windingTargets_ne
    (data.firstSigned source) (data.secondSigned source)
  calc
    (data.firstSigned source).target =
        sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 false)) := data.first_target source
    _ = sixVertexHorizontalDegreeTwoLoopHallTargetArrowPair
          (sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1
            (data.key source.1 true)) := harrows
    _ = (data.secondSigned source).target := (data.second_target source).symm


end SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
end
end StatMech.FrontierD
