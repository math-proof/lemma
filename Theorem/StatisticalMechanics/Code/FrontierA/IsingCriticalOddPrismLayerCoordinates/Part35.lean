/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part35


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismAgreementEndpointKernel_pos
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 < oddPrismAgreementEndpointKernel beta n a q := by
  unfold oddPrismAgreementEndpointKernel
  apply Finset.sum_pos
  · intro s _
    exact mul_pos
      (mul_pos (sq_pos_of_pos (oddPrismLayerHalfWeight_pos beta n s))
        (oddPrismUpperConditionedVector_pos beta n (ghsLMate a s)))
      (oddPrismUpperConditionedVector_pos beta n (ghsLMate q s))
  · exact Finset.univ_nonempty

theorem oddPrismAgreementEndpointKernel_symm
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismAgreementEndpointKernel beta n a q =
      oddPrismAgreementEndpointKernel beta n q a := by
  unfold oddPrismAgreementEndpointKernel
  apply Finset.sum_congr rfl
  intro s _
  ring


theorem oddPrismAgreementEndpointKernel_quadratic_eq
    (beta : Real) (n : Nat)
    (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
    (∑ a, ∑ q, f a * oddPrismAgreementEndpointKernel beta n a q * f q) =
      ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        (∑ a, f a * oddPrismUpperConditionedVector beta n (ghsLMate a s)) ^ 2 := by
  unfold oddPrismAgreementEndpointKernel
  calc
    (∑ a, ∑ q, f a *
        (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q) =
      ∑ a, ∑ q, ∑ s, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ s, ∑ q, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ = ∑ s, ∑ a, ∑ q, f a *
        (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      let g : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
        fun a => f a *
          oddPrismUpperConditionedVector beta n (ghsLMate a s)
      calc
        (∑ a, ∑ q, f a *
            (oddPrismLayerHalfWeight beta n s ^ 2 *
              oddPrismUpperConditionedVector beta n (ghsLMate a s) *
              oddPrismUpperConditionedVector beta n (ghsLMate q s)) * f q) =
          ∑ a, ∑ q,
            (oddPrismLayerHalfWeight beta n s ^ 2 * g a) * g q := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro q _
              unfold g
              ring
        _ = (∑ a, oddPrismLayerHalfWeight beta n s ^ 2 * g a) *
            ∑ q, g q := by
              rw [Fintype.sum_mul_sum]
        _ = oddPrismLayerHalfWeight beta n s ^ 2 * (∑ a, g a) ^ 2 := by
              rw [← Finset.mul_sum]
              ring
        _ = _ := by rfl

theorem oddPrismAgreementEndpointKernel_quadratic_nonneg
    (beta : Real) (n : Nat)
    (f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real) :
    0 <= ∑ a, ∑ q,
      f a * oddPrismAgreementEndpointKernel beta n a q * f q := by
  rw [oddPrismAgreementEndpointKernel_quadratic_eq]
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)


theorem oddPrismTransferAgreementFibreMass_eq_kernelTilt
    (beta : Real) (n : Nat) (hn : 0 < n)
    (q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismTransferAgreementFibreMass beta n q =
      ∑ a, oddPrismAgreementEndpointKernel beta n a q *
        Real.exp (beta * oddPrismTransferAgreementSpin n a) := by
  unfold oddPrismTransferAgreementFibreMass
  calc
    (∑ s, oddPrismLowerConditionedVector beta n s *
        oddPrismUpperConditionedVector beta n (ghsLMate q s)) =
      ∑ s, (oddPrismLayerHalfWeight beta n s ^ 2 *
          ∑ v, oddPrismPureSeamKernel beta n s v *
            oddPrismUpperConditionedVector beta n v) *
        oddPrismUpperConditionedVector beta n (ghsLMate q s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s]
    _ = ∑ s, ∑ a,
        oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperConditionedVector beta n (ghsLMate a s) *
          oddPrismUpperConditionedVector beta n (ghsLMate q s) *
          Real.exp (beta * oddPrismTransferAgreementSpin n a) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [← Equiv.sum_comp (ghsLMateEquiv s)]
      simp only [ghsLMateEquiv_apply]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      unfold oddPrismPureSeamKernel
      rw [oddPrismLayerSeamInteraction_mate]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      unfold oddPrismAgreementEndpointKernel
      rw [Finset.sum_mul]


theorem unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t -> t <= r ->
      unequalReplicaBridgeVariance G H K J hf hg t <=
        unequalReplicaBridgeVariance G H K J hf hg (-t)) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean G H K J hf hg t +
      unequalReplicaBridgeMean G H K J hf hg (-t)
  have hdiffD : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      G H K J hf hg t).differentiableAt
  have hanti : AntitoneOn D (Set.Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) r)
    · exact hdiffD.continuous.continuousOn
    · intro t _
      exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).deriv]
      exact sub_nonpos.mpr (hvar t ht.1.le ht.2.le)
  have hmean : forall t, 0 <= t -> t <= r -> D t <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    intro t ht htr
    have hle := hanti (by exact ⟨le_rfl, hr⟩) ⟨ht, htr⟩ ht
    dsimp only [D] at hle
    rw [neg_zero] at hle
    linarith
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos
    hdiffAll.continuous.continuousOn hdiffAll.differentiableOn
  have hderiv : deriv
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) c <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    rw [(hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg c).deriv]
    exact hmean c hc.1.le hc.2.le
  have hzero : unequalReplicaBridgeFreeEnergy G H K J hf hg 0 = 0 := by
    simp [unequalReplicaBridgeFreeEnergy]
  have hmul := mul_le_mul_of_nonneg_right hderiv hrpos.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hrpos.ne'] at hmul
  convert hmul using 1 <;> ring


theorem oddPrismUnequalBridgeFreeEnergy_le_of_transferVarianceOrder_Icc
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (hvar : forall t, 0 <= t -> t <= beta ->
      oddPrismTransferBridgeVariance beta n t <=
        oddPrismTransferBridgeVariance beta n (-t)) :
    oddPrismUnequalBridgeFreeEnergy beta n <=
      2 * beta * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  change unequalReplicaBridgeFreeEnergy
      (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
      (oddPrismUnequalGlueGraph n) beta
      (fun v => beta * oddPrismPlusField n v.1)
      (fun v => beta * oddPrismPlusField n v.1) beta <= _
  apply unequalReplicaBridgeFreeEnergy_le_of_variance_order_Icc
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n) beta
    (fun v => beta * oddPrismPlusField n v.1)
    (fun v => beta * oddPrismPlusField n v.1) beta hbeta
  intro t ht htb
  rw [oddPrismUnequalBridgeVariance_eq_transfer beta n hn t,
    oddPrismUnequalBridgeVariance_eq_transfer beta n hn (-t)]
  exact hvar t ht htb


end
end StatMech.FrontierA
