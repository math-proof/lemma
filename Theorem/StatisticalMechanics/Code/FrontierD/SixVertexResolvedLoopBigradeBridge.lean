/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedLoopBigradeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexExplicitResolvedMarkedPairEquivLoopMarked_bigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k) :
    sixVertexResolvedLoopMarkedPairBigrade
        (sixVertexExplicitResolvedMarkedPairEquivLoopMarked
          T left right k resolved) =
      sixVertexExplicitResolvedBigrade resolved := by
  let loopMarked := sixVertexExplicitResolvedMarkedPairEquivLoopMarked
    T left right k resolved
  let loops := loopMarked.1
  apply Prod.ext
  · change sixVertexLoopDecoratedPairTotalC loops =
      fkColoredLoopPairingPairTotalC
        (sixVertexExplicitResolvedColoredPair resolved)
    rw [← sixVertexLoopDecoratedPairColored_totalC]
    unfold fkColoredLoopPairingPairTotalC
    simp only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows,
      sixVertexExplicitResolvedColoredPair_arrows]
    change sixVertexTorusCTypeCount loops.1.1.1 +
        sixVertexTorusCTypeCount loops.1.2.1 =
      sixVertexTorusCTypeCount resolved.1.1.1.1 +
        sixVertexTorusCTypeCount resolved.1.1.2.1
    have hpair : loops.1 = resolved.1.1 := rfl
    rw [hpair]
  · change fkColoredTrueStrandSlotCount
        (sixVertexLoopDecoratedPairColored loops) =
      fkColoredTrueStrandSlotCount
        (sixVertexExplicitResolvedColoredPair resolved)
    apply Fintype.card_congr
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro slot
    change (fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored loops) slot = true) ↔ _
    have hcolor : fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored loops) slot =
      fkColoredLayeredSlotColor
        (sixVertexExplicitResolvedColoredPair resolved) slot := by
      rcases slot with ⟨layer, v, side⟩
      cases layer <;> rfl
    simp [hcolor]

end
end StatMech.FrontierD
