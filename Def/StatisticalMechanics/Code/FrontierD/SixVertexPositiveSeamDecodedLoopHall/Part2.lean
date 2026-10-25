/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamWindingFlows.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection

def toRoutedReconnection
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnection
      T middle hmiddle_pos hmiddle_lt grade where
  key := data.key
  source_recoverable := by
    intro first firstBranch second secondBranch heq
    exact data.source_recoverable first second firstBranch secondBranch heq
  high_distinct := data.high_distinct

end SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection


def SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection
      T middle hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
