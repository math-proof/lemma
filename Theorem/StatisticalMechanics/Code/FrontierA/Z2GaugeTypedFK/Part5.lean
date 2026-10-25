/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part2
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedESWeight_sum_sigma_signed_eq_indicator
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      if omega ∈ typedFKConsistencyEvent ends D then
        ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega
      else 0 := by
  classical
  by_cases h : omega ∈ typedFKConsistencyEvent ends D
  · rw [if_pos h]
    obtain ⟨witness, hw⟩ := h
    exact typedESWeight_sum_sigma_signed_eq_ordinary_of_witness
      ends rho D omega witness hw
  · rw [if_neg h]
    rw [typedESWeight_sum_sigma_eq_activity_mul_card]
    have hnone : forall sigma : V -> Bool,
        ¬ TypedSignedCompatible ends D omega sigma := by
      intro sigma hsigma
      exact h ⟨sigma, hsigma⟩
    simp [hnone]


end
end StatMech.FrontierA
