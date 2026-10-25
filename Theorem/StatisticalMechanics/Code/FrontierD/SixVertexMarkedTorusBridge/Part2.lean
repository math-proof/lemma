/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTorusBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusMarkedWeight_eq_pow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) :
    sixVertexTorusMarkedWeight omega =
      (C 2 + X) ^ sixVertexTorusCTypeCount omega := by
  unfold sixVertexTorusMarkedWeight sixVertexTorusCTypeCount
  simp_rw [sixVertexLocalMarkedPatternWeight_eq_pow _
    (sixVertexLocalIncomingPattern_ice omega homega _)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  simp only [sixVertexLocalIncomingPattern_isCType_iff]

theorem sixVertexTorusMarkedWeight_eq_zero_of_not_ice
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : ¬ omega.IceRule) :
    sixVertexTorusMarkedWeight omega = 0 := by
  classical
  simp only [SixVertexArrows.IceRule, not_forall] at homega
  obtain ⟨v, hv⟩ := homega
  have hpattern : ¬ (sixVertexLocalIncomingPattern omega v).Ice := by
    rw [SixVertexLocalIncomingPattern.Ice,
      sixVertexLocalIncomingPattern_count]
    exact hv
  have hzero : sixVertexLocalMarkedPatternWeight
      (sixVertexLocalIncomingPattern omega v) = 0 := by
    simp [sixVertexLocalMarkedPatternWeight, hpattern]
  exact Finset.prod_eq_zero (Finset.mem_univ v) hzero

theorem coeff_sixVertexTorusMarkedWeight
    {T : EvenTorus} (omega : SixVertexArrows T) (k : Nat) :
    (sixVertexTorusMarkedWeight omega).coeff k =
      if omega.IceRule then
        (2 : Real) ^ (sixVertexTorusCTypeCount omega - k) *
          (sixVertexTorusCTypeCount omega).choose k
      else 0 := by
  classical
  by_cases homega : omega.IceRule
  · rw [if_pos homega, sixVertexTorusMarkedWeight_eq_pow omega homega,
      coeff_two_add_X_pow]
  · rw [if_neg homega]
    rw [sixVertexTorusMarkedWeight_eq_zero_of_not_ice omega homega]
    simp

theorem eval_sixVertexTorusMarkedWeight
    {T : EvenTorus} (t : Real) (omega : SixVertexArrows T) :
    eval t (sixVertexTorusMarkedWeight omega) =
      omega.weight (2 + t) := by
  change (evalRingHom t) (sixVertexTorusMarkedWeight omega) = _
  rw [sixVertexTorusMarkedWeight, map_prod, SixVertexArrows.weight]
  apply Finset.prod_congr rfl
  intro v hv
  change eval t
      (sixVertexLocalMarkedPatternWeight
        (sixVertexLocalIncomingPattern omega v)) = _
  rw [eval_sixVertexLocalMarkedPatternWeight,
    sixVertexLocalPatternWeight_eq_localWeight]


end
end StatMech.FrontierD
