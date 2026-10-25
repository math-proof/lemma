/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairBigrade.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedLoopBigradeBridge.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexCompatibleLoopPairingPairEquivFin
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right)
    (total : Nat) (htotal : sixVertexConfigurationPairTotalC pair = total) :
    (SixVertexCompatibleLoopPairing pair.1.1 ×
      SixVertexCompatibleLoopPairing pair.2.1) ≃ Fin (2 ^ total) := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_prod,
    card_sixVertexCompatibleLoopPairing pair.1.1 pair.1.2.1,
    card_sixVertexCompatibleLoopPairing pair.2.1 pair.2.2.1,
    Fintype.card_fin, ← pow_add]
  exact congrArg (fun n : Nat => 2 ^ n) htotal

noncomputable def sixVertexLoopDecoratedPairBigradeFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    {decorated : SixVertexLoopDecoratedPair T left right //
        sixVertexLoopDecoratedPairBigrade decorated = grade} ≃
      ({pair : SixVertexMarkedSectorConfiguration T left ×
          SixVertexMarkedSectorConfiguration T right //
          sixVertexConfigurationPairBigrade pair = grade} ×
        Fin (2 ^ grade.1)) where
  toFun decorated :=
    let hgrade : sixVertexConfigurationPairBigrade decorated.1.1 = grade := by
      simpa [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
        using decorated.2
    let htotal : sixVertexConfigurationPairTotalC decorated.1.1 = grade.1 :=
      congrArg Prod.fst hgrade
    (⟨decorated.1.1, hgrade⟩,
      sixVertexCompatibleLoopPairingPairEquivFin
        decorated.1.1 grade.1 htotal decorated.1.2)
  invFun decorated :=
    let htotal : sixVertexConfigurationPairTotalC decorated.1.1 = grade.1 :=
      congrArg Prod.fst decorated.1.2
    ⟨⟨decorated.1.1,
        (sixVertexCompatibleLoopPairingPairEquivFin
          decorated.1.1 grade.1 htotal).symm decorated.2⟩,
      by
        rw [sixVertexLoopDecoratedPairBigrade_eq_configurationPair]
        exact decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · simp

end
end StatMech.FrontierD
