/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FK.PositiveAssociation
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectCriticalEdgeFactor_pos (R : FKRectTorus)
    {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalEdgeFactor R q := by
  unfold fkRectCriticalEdgeFactor
  positivity


theorem fkWeight_configurationExtend_critical
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    FK.fkWeight (fkRectTorusGraph R) (fkRectCriticalP q) q
        (fkRectGraphConfigurationExtend R eta) =
      fkRectCriticalEdgeFactor R q *
        fkRectGraphCriticalReducedWeight R q eta := by
  let omega := (fkRectConfigurationGraphEquiv R).symm eta
  have hweight := fkWeight_configurationGraphEquiv R
    (fkRectCriticalP q) q omega
  have hcritical := fkRectRandomClusterWeight_critical_eq R hq omega
  rw [hcritical] at hweight
  rw [← fkRectGraphCriticalReducedWeight_configurationGraphEquiv
    R q omega] at hweight
  rw [show fkRectConfigurationGraphEquiv R omega = eta by
    exact (fkRectConfigurationGraphEquiv R).apply_symm_apply eta] at hweight
  simpa [fkRectCriticalEdgeFactor] using hweight


theorem fkRectGraphCriticalReducedWeight_logSupermodular
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphCriticalReducedWeight R q eta *
        fkRectGraphCriticalReducedWeight R q zeta ≤
      fkRectGraphCriticalReducedWeight R q (eta ⊔ zeta) *
        fkRectGraphCriticalReducedWeight R q (eta ⊓ zeta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp := fkRectCriticalP_pos hq0
  have hp1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_logSupermodular (fkRectTorusGraph R)
    hp hp1 hq
    (fkRectGraphConfigurationExtend R eta)
    (fkRectGraphConfigurationExtend R zeta)
  rw [← fkRectGraphConfigurationExtend_sup,
    ← fkRectGraphConfigurationExtend_inf] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  nlinarith [sq_pos_of_pos hfactor]

theorem fkRectGraphCriticalReducedWeight_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    0 < fkRectGraphCriticalReducedWeight R q eta := by
  unfold fkRectGraphCriticalReducedWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectGraphCriticalReducedZ_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectGraphCriticalReducedZ R q := by
  rw [fkRectGraphCriticalReducedZ_eq]
  exact fkRectCriticalReducedZ_pos R hq

theorem fkRectGraphCriticalRandomClusterProb_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (eta : FKRectGraphConfiguration R) :
    0 ≤ fkRectGraphCriticalRandomClusterProb R q eta :=
  (div_pos (fkRectGraphCriticalReducedWeight_pos R hq eta)
    (fkRectGraphCriticalReducedZ_pos R hq)).le

theorem sum_fkRectGraphCriticalRandomClusterProb
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    ∑ eta : FKRectGraphConfiguration R,
      fkRectGraphCriticalRandomClusterProb R q eta = 1 := by
  calc
    (∑ eta : FKRectGraphConfiguration R,
        fkRectGraphCriticalRandomClusterProb R q eta) =
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega := by
      symm
      apply Fintype.sum_equiv (fkRectConfigurationGraphEquiv R)
      intro omega
      exact
        (fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv
          R q omega).symm
    _ = 1 := sum_fkRectCriticalRandomClusterProb R hq

@[simp] theorem fkRectConfigurationGraphEquiv_inf
    (R : FKRectTorus) (omega tau : R.Configuration) :
    fkRectConfigurationGraphEquiv R (omega ⊓ tau) =
      fkRectConfigurationGraphEquiv R omega ⊓
        fkRectConfigurationGraphEquiv R tau := by
  funext e
  rfl

@[simp] theorem fkRectConfigurationGraphEquiv_sup
    (R : FKRectTorus) (omega tau : R.Configuration) :
    fkRectConfigurationGraphEquiv R (omega ⊔ tau) =
      fkRectConfigurationGraphEquiv R omega ⊔
        fkRectConfigurationGraphEquiv R tau := by
  funext e
  rfl


theorem fkRectGraphCriticalRandomClusterProb_fkgLattice
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (eta zeta : FKRectGraphConfiguration R) :
    fkRectGraphCriticalRandomClusterProb R q eta *
        fkRectGraphCriticalRandomClusterProb R q zeta ≤
      fkRectGraphCriticalRandomClusterProb R q (eta ⊓ zeta) *
        fkRectGraphCriticalRandomClusterProb R q (eta ⊔ zeta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [div_mul_div_comm, div_mul_div_comm]
  apply (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).2
  simpa [mul_comm] using
    fkRectGraphCriticalReducedWeight_logSupermodular R hq eta zeta


theorem fkRectCriticalRandomClusterProb_fkgLattice
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (omega tau : R.Configuration) :
    fkRectCriticalRandomClusterProb R q omega *
        fkRectCriticalRandomClusterProb R q tau ≤
      fkRectCriticalRandomClusterProb R q (omega ⊓ tau) *
        fkRectCriticalRandomClusterProb R q (omega ⊔ tau) := by
  simpa only [
      ← fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv,
      fkRectConfigurationGraphEquiv_inf,
      fkRectConfigurationGraphEquiv_sup] using
    fkRectGraphCriticalRandomClusterProb_fkgLattice R hq
      (fkRectConfigurationGraphEquiv R omega)
      (fkRectConfigurationGraphEquiv R tau)


theorem fkRectGraphCritical_positivelyAssociated
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {f g : FKRectGraphConfiguration R → Real}
    (hf : Monotone f) (hg : Monotone g) :
    (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * f eta) *
        (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * g eta) ≤
      ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta *
        (f eta * g eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Probability.fkg_inequality
    (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R hq0 eta)
    (sum_fkRectGraphCriticalRandomClusterProb R hq0)
    (fkRectGraphCriticalRandomClusterProb_fkgLattice R hq) hf hg


theorem fkRectCritical_positivelyAssociated
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {f g : R.Configuration → Real}
    (hf : Monotone f) (hg : Monotone g) :
    (∑ omega, fkRectCriticalRandomClusterProb R q omega * f omega) *
        (∑ omega, fkRectCriticalRandomClusterProb R q omega * g omega) ≤
      ∑ omega, fkRectCriticalRandomClusterProb R q omega *
        (f omega * g omega) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact Probability.fkg_inequality
    (fkRectCriticalRandomClusterProb_nonneg R hq0)
    (sum_fkRectCriticalRandomClusterProb R hq0)
    (fkRectCriticalRandomClusterProb_fkgLattice R hq) hf hg

end
end StatMech.FrontierD
