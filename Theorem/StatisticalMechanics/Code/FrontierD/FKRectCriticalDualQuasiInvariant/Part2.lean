/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualPreimageEvent_isIncreasing
    (R : FKRectTorus) {A : Set R.Configuration} (hA : IsDecreasing A) :
    IsIncreasing (fkRectDualPreimageEvent R A) := by
  intro omega tau hot homega
  exact hA (fkRectDualConfigurationEquiv_antitone R hot) homega

theorem fkRectDualEvent_dualPreimageEvent
    (R : FKRectTorus) (A : Set R.Configuration) :
    fkRectDualEvent R (fkRectDualPreimageEvent R A) = A := by
  ext eta
  constructor
  · rintro ⟨omega, homega, rfl⟩
    exact homega
  · intro heta
    exact ⟨(fkRectDualConfigurationEquiv R).symm eta, by
      simpa [fkRectDualPreimageEvent] using heta,
      (fkRectDualConfigurationEquiv R).apply_symm_apply eta⟩


theorem fkRectCriticalEventMass_dualEvent_eq
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectDualEvent R A) =
      ∑ omega : R.Configuration,
        A.indicator (fun omega =>
          fkRectCriticalRandomClusterProb R q
            (fkRectDualConfigurationEquiv R omega)) omega := by
  classical
  unfold fkRectCriticalEventMass
  apply Fintype.sum_equiv (fkRectDualConfigurationEquiv R).symm
  intro eta
  by_cases hA : (fkRectDualConfigurationEquiv R).symm eta ∈ A
  · have hdual : eta ∈ fkRectDualEvent R A := by
      exact ⟨(fkRectDualConfigurationEquiv R).symm eta, hA,
        (fkRectDualConfigurationEquiv R).apply_symm_apply eta⟩
    rw [Set.indicator_of_mem hdual, Set.indicator_of_mem hA]
    simp
  · have hdual : eta ∉ fkRectDualEvent R A := by
      rintro ⟨omega, homega, rfl⟩
      exact hA (by simpa using homega)
    rw [Set.indicator_of_notMem hdual, Set.indicator_of_notMem hA]


theorem fkRectCriticalEventMass_dualEvent_le
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q (fkRectDualEvent R A) ≤
      q * fkRectCriticalEventMass R q A := by
  rw [fkRectCriticalEventMass_dualEvent_eq,
    fkRectCriticalEventMass_eq_indicatorExpectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simpa using fkRectCriticalRandomClusterProb_dual_le R hq omega
  · simp [Set.indicator_of_notMem hA]

theorem fkRectCriticalEventMass_le_q_mul_dualEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q (fkRectDualEvent R A) := by
  rw [fkRectCriticalEventMass_dualEvent_eq,
    fkRectCriticalEventMass_eq_indicatorExpectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simpa using fkRectCriticalRandomClusterProb_le_q_mul_dual R hq omega
  · simp [Set.indicator_of_notMem hA]


theorem one_div_q_mul_eventMass_le_of_dualEvent_subset
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    {A B : Set R.Configuration} (hAB : fkRectDualEvent R A ⊆ B) :
    (1 / q) * fkRectCriticalEventMass R q A <=
      fkRectCriticalEventMass R q B := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq A
  have hmono := fkRectCriticalEventMass_mono R hq0 hAB
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hq0]
  exact hdual.trans (by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hmono hq0.le)


theorem one_div_one_add_q_le_eventMass_of_compl_subset_dualEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) (hcover : Aᶜ ⊆ fkRectDualEvent R A) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmono := fkRectCriticalEventMass_mono R hq0 hcover
  have hdual := fkRectCriticalEventMass_dualEvent_le R hq A
  rw [fkRectCriticalEventMass_compl R hq0 A] at hmono
  have hbasic : 1 - fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q A := hmono.trans hdual
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith


theorem one_div_one_add_q_le_eventMass_of_dualCompl_subset
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration)
    (hcover : fkRectDualEvent R Aᶜ ⊆ A) :
    1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hdual := fkRectCriticalEventMass_le_q_mul_dualEvent R hq Aᶜ
  have hmono := fkRectCriticalEventMass_mono R hq0 hcover
  rw [fkRectCriticalEventMass_compl R hq0 A] at hdual
  have hbasic : 1 - fkRectCriticalEventMass R q A ≤
      q * fkRectCriticalEventMass R q A :=
    hdual.trans (mul_le_mul_of_nonneg_left hmono (zero_le_one.trans hq))
  have hden : 0 < 1 + q := by linarith
  rw [div_le_iff₀ hden]
  nlinarith

end
end StatMech.FrontierD
