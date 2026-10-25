/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalSymmetricMean.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

theorem unequalReplicaBridgeFreeEnergy_le_of_symmetric_mean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hmean : forall t, 0 <= t -> t <= r ->
      unequalReplicaBridgeMean G H K J hf hg t +
          unequalReplicaBridgeMean G H K J hf hg (-t) <=
        2 * unequalReplicaBridgeMean G H K J hf hg 0) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  have hcont : ContinuousOn
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) (Icc 0 r) :=
    hdiffAll.continuous.continuousOn
  have hdiff : DifferentiableOn Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) (Ioo 0 r) :=
    hdiffAll.differentiableOn
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos hcont hdiff
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
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul


end
end StatMech.FrontierA
