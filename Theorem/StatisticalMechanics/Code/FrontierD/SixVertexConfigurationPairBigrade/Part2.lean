/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2


namespace StatMech.FrontierD

noncomputable section

theorem loopBigradeFibers_of_configurationBigradeFibers
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (hfiber : SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexLoopDecoratedPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  intro grade
  rw [card_sixVertexLoopDecoratedPairBigradeFiber,
    card_sixVertexLoopDecoratedPairBigradeFiber]
  exact Nat.mul_le_mul_right (2 ^ grade.1) (hfiber grade)


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexConfigurationPairBigradeFiberDominates T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (loopBigradeFibers_of_configurationBigradeFibers hfiber)

end
end StatMech.FrontierD
