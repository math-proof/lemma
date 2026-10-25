/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRepairDecodedLoopHall


namespace StatMech.FrontierD

noncomputable section

theorem degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexHorizontalDegreeTwoLoopRoutedReconnections
      T middle hmiddle_pos hmiddle_lt := by
  intro grade
  obtain ⟨repair⟩ := hrepairs grade
  exact ⟨repair.toRoutedReconnection⟩

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedHorizontalRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_degreeTwoLoopRoutedReconnections
    T middle hmiddle_pos hmiddle_lt
    (degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs
      T middle hmiddle_pos hmiddle_lt hrepairs)

end
end StatMech.FrontierD
