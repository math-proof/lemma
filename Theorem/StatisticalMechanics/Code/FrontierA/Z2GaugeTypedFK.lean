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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part2
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedESWeight_sum_omega (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) :
    (∑ omega : P -> Bool, typedESWeight ends rho D sigma omega) =
      ∏ p : P, ∑ b : Bool, typedESEdgeFactor ends rho D sigma p b := by
  unfold typedESWeight
  exact (Fintype.prod_sum _).symm

theorem typedESEdgeFactor_sum_bool (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (p : P) :
    (∑ b : Bool, typedESEdgeFactor ends rho D sigma p b) =
      if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1 else 1 - rho p := by
  rw [Fintype.sum_bool]
  unfold typedESEdgeFactor
  by_cases h : sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D
  · simp [h]
  · simp [h]

theorem typedESWeight_sum_omega_eq_shiftedCut
    (ends : P -> V × V) (J : P -> Real) (D : Finset P)
    (sigma : V -> Bool) :
    (∑ omega : P -> Bool,
      typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) D sigma omega) =
      ∏ p ∈ multibondCut ends sigma ∆ D, Real.exp (-2 * J p) := by
  rw [typedESWeight_sum_omega]
  simp_rw [typedESEdgeFactor_sum_bool]
  have hpoint : forall p : P,
      (if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1
        else 1 - (1 - Real.exp (-2 * J p))) =
      if p ∈ multibondCut ends sigma ∆ D then Real.exp (-2 * J p) else 1 := by
    intro p
    by_cases hs : sigma (ends p).1 = sigma (ends p).2 <;>
      by_cases hD : p ∈ D <;>
      simp [multibondCut, hs, hD, Finset.mem_symmDiff]
  simp_rw [hpoint]
  rw [Finset.prod_ite_mem]
  simp


theorem multibondIsingPartition_twist_eq_exp_mul_typedESZ
    (ends : P -> V × V) (J : P -> Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) =
      Real.exp (∑ p : P, J p) *
        typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) D := by
  unfold multibondIsingPartition typedESZ
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [multibondIsingWeight_twist_eq_shiftedActivity]
  congr 1
  exact (typedESWeight_sum_omega_eq_shiftedCut ends J D sigma).symm


end
end StatMech.FrontierA
