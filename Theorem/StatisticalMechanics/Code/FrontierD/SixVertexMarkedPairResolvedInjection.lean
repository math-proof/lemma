/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexExplicitResolvedColoredPair_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    (sixVertexExplicitResolvedColoredPair resolved layer).arrows =
      sixVertexArrowPairLayer resolved.1.1.1.1
        resolved.1.1.2.1 layer := by
  exact SixVertexCompatibleLoopPairing.toColored_arrows _

@[simp] theorem sixVertexExplicitResolvedColoredPair_pairing
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T left right k)
    (layer : Bool) :
    (sixVertexExplicitResolvedColoredPair resolved layer).pairing =
      sixVertexExplicitResolvedPairing
        resolved.1.2 resolved.2 layer :=
  rfl

theorem card_sixVertexExplicitResolvedMarkedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype.card
        (SixVertexExplicitResolvedMarkedPair T left right k) =
      Fintype.card
          (SixVertexExplicitMarkedDecoratedPair T left right k) * 2 ^ k := by
  rw [Fintype.card_sigma]
  simp_rw [card_sixVertexExplicitMarkedResolution]
  simp

theorem markedResolutionFactor_identity (total k : Nat) :
    (2 ^ (total - k) * total.choose k) * 2 ^ k =
      2 ^ total * total.choose k := by
  by_cases hk : k <= total
  · calc
      (2 ^ (total - k) * total.choose k) * 2 ^ k =
          (2 ^ (total - k) * 2 ^ k) * total.choose k := by
            ac_rfl
      _ = 2 ^ total * total.choose k := by
        rw [Nat.pow_sub_mul_pow 2 hk]
  · have hchoose : total.choose k = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hchoose]


end
end StatMech.FrontierD
