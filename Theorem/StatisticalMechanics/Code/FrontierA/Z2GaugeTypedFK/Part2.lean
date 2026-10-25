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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part3
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedESWeight_factor (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (omega : P -> Bool) :
    typedESWeight ends rho D sigma omega =
      typedESActivity rho omega *
        (if TypedSignedCompatible ends D omega sigma then 1 else 0) := by
  unfold typedESWeight typedESActivity
  by_cases hcompat : TypedSignedCompatible ends D omega sigma
  · rw [if_pos hcompat]
    simp only [mul_one]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : omega p
    · have hrel := hcompat p (by simpa using hp)
      simp [typedESEdgeFactor, hp, hrel]
    · simp [typedESEdgeFactor, hp]
  · rw [if_neg hcompat, mul_zero]
    classical
    simp only [TypedSignedCompatible] at hcompat
    push Not at hcompat
    obtain ⟨p, hp⟩ := hcompat
    rw [Finset.prod_eq_zero_iff]
    refine ⟨p, Finset.mem_univ p, ?_⟩
    have hrel : ¬ (sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D) := by
      rcases hp.2 with ⟨heq, hD⟩ | ⟨hne, hnotD⟩
      · simp [heq, hD]
      · simp [hne, hnotD]
    simp [typedESEdgeFactor, hp.1, hrel]


end
end StatMech.FrontierA
