/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3


namespace StatMech.FrontierD

noncomputable section

theorem resolvedBigradeFibers_of_loopBigradeFibers
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexExplicitResolvedBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  intro k grade
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card {source : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k //
      sixVertexExplicitResolvedBigrade source = grade} =
        Fintype.card
            {loops : SixVertexLoopDecoratedPair T sourceLeft sourceRight //
              sixVertexLoopDecoratedPairBigrade loops = grade} *
          grade.1.choose k :=
      card_sixVertexExplicitResolvedBigradeFiber
        T sourceLeft sourceRight k grade
    _ <= Fintype.card
            {loops : SixVertexLoopDecoratedPair T targetLeft targetRight //
              sixVertexLoopDecoratedPairBigrade loops = grade} *
          grade.1.choose k :=
      Nat.mul_le_mul_right (grade.1.choose k) (hfiber grade)
    _ = Fintype.card {target : SixVertexExplicitResolvedMarkedPair
        T targetLeft targetRight k //
      sixVertexExplicitResolvedBigrade target = grade} :=
      (card_sixVertexExplicitResolvedBigradeFiber
        T targetLeft targetRight k grade).symm


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopBigradeFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexLoopDecoratedPairBigradeFiberDominates T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (resolvedBigradeFibers_of_loopBigradeFibers hfiber)

end
end StatMech.FrontierD
