/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part2


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexExplicitResolvedBigradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat)
    (grade : Nat × Nat) :
    Fintype.card
        {resolved : SixVertexExplicitResolvedMarkedPair T left right k //
          sixVertexExplicitResolvedBigrade resolved = grade} =
      Fintype.card
          {loops : SixVertexLoopDecoratedPair T left right //
            sixVertexLoopDecoratedPairBigrade loops = grade} *
        grade.1.choose k := by
  rw [Fintype.card_congr
      (sixVertexExplicitResolvedBigradeFiberEquivLoopMarked
        T left right k grade),
    Fintype.card_congr
      (sixVertexResolvedLoopMarkedBigradeFiberEquiv
        T left right k grade)]
  simp


end
end StatMech.FrontierD
