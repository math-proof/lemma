/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexResolvedDecorationEquivLoopPairingsMarked
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) (k : Nat) :
    (Sigma fun decoration : SixVertexExplicitMarkedPairDecoration
        pair.1.1 pair.2.1 k =>
      SixVertexExplicitMarkedResolution decoration) ≃
      (Sigma fun _pairings :
          SixVertexCompatibleLoopPairing pair.1.1 ×
            SixVertexCompatibleLoopPairing pair.2.1 =>
        Fin ((sixVertexConfigurationPairTotalC pair).choose k)) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_sigma, Fintype.card_sigma]
  simp_rw [card_sixVertexExplicitMarkedResolution]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_sixVertexExplicitMarkedPairDecoration]
  simp only [Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_prod,
    card_sixVertexCompatibleLoopPairing pair.1.1 pair.1.2.1,
    card_sixVertexCompatibleLoopPairing pair.2.1 pair.2.2.1]
  rw [← pow_add]
  exact markedResolutionFactor_identity
    (sixVertexConfigurationPairTotalC pair) k


noncomputable def sixVertexExplicitResolvedMarkedPairEquivLoopMarked
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    SixVertexExplicitResolvedMarkedPair T left right k ≃
      SixVertexResolvedLoopMarkedPair T left right k :=
  (Equiv.sigmaAssoc fun
      (pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right)
      (decoration : SixVertexExplicitMarkedPairDecoration
        pair.1.1 pair.2.1 k) =>
      SixVertexExplicitMarkedResolution decoration).trans
    ((Equiv.sigmaCongrRight fun pair =>
      sixVertexResolvedDecorationEquivLoopPairingsMarked pair k).trans
    (Equiv.sigmaAssoc fun
      (pair : SixVertexMarkedSectorConfiguration T left ×
        SixVertexMarkedSectorConfiguration T right)
      (_pairings : SixVertexCompatibleLoopPairing pair.1.1 ×
        SixVertexCompatibleLoopPairing pair.2.1) =>
      Fin ((sixVertexConfigurationPairTotalC pair).choose k)).symm)

end
end StatMech.FrontierD
