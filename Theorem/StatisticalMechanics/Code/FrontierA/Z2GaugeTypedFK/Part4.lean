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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part5
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedESWeight_sum_sigma_eq_activity_mul_card
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      typedESActivity rho omega *
        ((Finset.univ.filter
          (TypedSignedCompatible ends D omega)).card : Real) := by
  simp_rw [typedESWeight_factor]
  rw [← Finset.mul_sum, Finset.sum_boole]

theorem typedESWeight_sum_sigma_signed_eq_ordinary_of_witness
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    (omega : P -> Bool) (witness : V -> Bool)
    (hw : TypedSignedCompatible ends D omega witness) :
    (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) =
      ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega := by
  rw [typedESWeight_sum_sigma_eq_activity_mul_card,
    typedESWeight_sum_sigma_eq_activity_mul_card]
  congr 1
  norm_cast
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (typedSignedCompatibleEquiv ends D omega witness hw)


end
end StatMech.FrontierA
