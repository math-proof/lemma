/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing
    (beta : Real) (n : Nat) (r : Real)
    (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
    oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
  rw [oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp]
  exact finiteExpVarianceSkew_nonpos_of_switchingPairing
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r hpair


theorem oddPrismTransferBridgeVariance_le_neg_of_switchingPairing
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
    oddPrismTransferBridgeVariance beta n r <=
      oddPrismTransferBridgeVariance beta n (-r) := by
  rw [oddPrismTransferBridgeVariance_le_neg_iff_skewNumerator_nonpos
    beta n hn r]
  exact
    oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing
      beta n r hpair


theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc
    {beta : Real} (hbeta : 0 <= beta) {n : Nat}
    (hvar : forall t, 0 <= t -> t <= beta ->
      unequalReplicaBridgeVariance
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) beta
          (fun v => beta * oddPrismPlusField n v.1)
          (fun v => beta * oddPrismPlusField n v.1) t <=
        unequalReplicaBridgeVariance
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) beta
          (fun v => beta * oddPrismPlusField n v.1)
          (fun v => beta * oddPrismPlusField n v.1) (-t)) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) t +
      unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) (-t)
  have hdiff : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta _ _ t).differentiableAt
  have hanti : AntitoneOn D (Icc 0 beta) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) beta)
    · exact hdiff.continuous.continuousOn
    · intro t _
      exact hdiff t |>.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta _ _ t).deriv]
      exact sub_nonpos.mpr (hvar t ht.1.le ht.2.le)
  intro t ht htbeta
  have hle := hanti (by exact ⟨le_rfl, hbeta⟩) ⟨ht, htbeta⟩ ht
  dsimp only [D] at hle
  rw [neg_zero] at hle
  linarith


theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings
    {beta : Real} (hbeta : 0 <= beta) {n : Nat} (hn : 0 < n)
    (hpair : forall t, 0 <= t -> t <= beta ->
      OddPrismTransferSkewSwitchingPairing beta n t) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  apply oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc hbeta
  intro t ht htbeta
  rw [oddPrismUnequalBridgeVariance_eq_transfer beta n hn t,
    oddPrismUnequalBridgeVariance_eq_transfer beta n hn (-t)]
  exact oddPrismTransferBridgeVariance_le_neg_of_switchingPairing
    beta n hn t (hpair t ht htbeta)


theorem oddPrismUnequalBridgeSymmetricMeanOrder_all_of_transferSwitchingPairings
    {beta : Real} (hbeta : 0 <= beta)
    (hpair : forall n, 0 < n -> forall t, 0 <= t -> t <= beta ->
      OddPrismTransferSkewSwitchingPairing beta n t) :
    forall n, OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · exact oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism beta
  · exact oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings
      hbeta hn (hpair n hn)


theorem oddPrismUnequalBridgeSymmetricMeanOrder_of_nonpos
    {beta : Real} (hbeta : beta <= 0) (n : Nat) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
  intro t ht htbeta
  have ht0 : t <= 0 := htbeta.trans hbeta
  have htzero : t = 0 := le_antisymm ht0 ht
  subst t
  simp only [neg_zero, two_mul]
  exact le_rfl

end
end StatMech.FrontierA
