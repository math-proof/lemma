/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRepairDecodedLoopHall


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair

def toRoutedReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  key := data.key
  source_recoverable := by
    intro first firstBranch second secondBranch heq
    exact data.source_recoverable first second firstBranch secondBranch heq
  high_distinct := data.high_distinct

end SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair

def SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty (SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair
    T middle hmiddle_pos hmiddle_lt grade)

end
end StatMech.FrontierD
