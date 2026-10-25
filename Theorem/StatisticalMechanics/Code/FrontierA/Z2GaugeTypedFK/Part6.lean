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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part7
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedFKZ_eq_typedESZ_empty (ends : P -> V × V) (rho : P -> Real) :
    typedFKZ ends rho = typedESZ ends rho ∅ := rfl

theorem typedESZ_eq_typedFKWeight_filter
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P) :
    typedESZ ends rho D =
      ∑ omega : P -> Bool,
        typedFKWeight ends rho omega *
          (typedFKConsistencyEvent ends D).indicator
            (fun _ => (1 : Real)) omega := by
  unfold typedESZ typedFKWeight
  apply Finset.sum_congr rfl
  intro omega _
  rw [typedESWeight_sum_sigma_signed_eq_indicator]
  by_cases h : omega ∈ typedFKConsistencyEvent ends D
  · simp [h]
  · simp [h]

theorem typedFKZ_pos_of_coupling (ends : P -> V × V) (J : P -> Real) :
    0 < typedFKZ ends (fun p => 1 - Real.exp (-2 * J p)) := by
  have hpart := multibondIsingPartition_twist_eq_exp_mul_typedESZ
    ends J (∅ : Finset P)
  have hprod : 0 < Real.exp (∑ p : P, J p) *
      typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅ := by
    rw [← hpart]
    have htwist : multibondTwistCoupling J (∅ : Finset P) = J := by
      ext p
      simp [multibondTwistCoupling]
    simpa [htwist] using multibondIsingPartition_pos ends J
  have hexp : 0 < Real.exp (∑ p : P, J p) := Real.exp_pos _
  have hZ : 0 < typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) ∅ := by
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.2
    · exact (not_lt_of_ge hexp.le h.1).elim
  simpa [typedFKZ_eq_typedESZ_empty] using hZ

theorem typedFKProb_nonneg_of_nonneg
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) (omega : P -> Bool) :
    0 <= typedFKProb ends rho omega := by
  apply div_nonneg
  · unfold typedFKWeight
    apply Finset.sum_nonneg
    intro sigma _
    unfold typedESWeight typedESEdgeFactor
    apply Finset.prod_nonneg
    intro p _
    by_cases hp : omega p
    · by_cases heq : sigma (ends p).1 = sigma (ends p).2
      · simp [hp, heq, hrho0 p]
      · simp [hp, heq]
    · have hpfalse : omega p = false := Bool.eq_false_of_not_eq_true hp
      simp [hpfalse, sub_nonneg.mpr (hrho1 p)]
  · exact hZ.le

theorem typedFKProb_sum_eq_one
    (ends : P -> V × V) (rho : P -> Real)
    (hZ : typedFKZ ends rho ≠ 0) :
    (∑ omega : P -> Bool, typedFKProb ends rho omega) = 1 := by
  unfold typedFKProb
  rw [← Finset.sum_div]
  change typedFKZ ends rho / typedFKZ ends rho = 1
  exact div_self hZ

theorem typedESZ_div_eq_consistencyMass
    (ends : P -> V × V) (rho : P -> Real) (D : Finset P)
    :
    typedESZ ends rho D / typedESZ ends rho ∅ =
      typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
  rw [typedESZ_eq_typedFKWeight_filter]
  unfold typedFKEventMass typedFKProb
  rw [typedFKZ_eq_typedESZ_empty]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega _
  ring


theorem multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass
    (ends : P -> V × V) (J : P -> Real) (D : Finset P) :
    multibondIsingPartition ends (multibondTwistCoupling J D) /
        multibondIsingPartition ends J =
      typedFKEventMass ends (fun p => 1 - Real.exp (-2 * J p))
        (typedFKConsistencyEvent ends D) := by
  let rho := fun p => 1 - Real.exp (-2 * J p)
  have hnum := multibondIsingPartition_twist_eq_exp_mul_typedESZ ends J D
  have hden0 := multibondIsingPartition_twist_eq_exp_mul_typedESZ
    ends J (∅ : Finset P)
  have hden : multibondIsingPartition ends J =
      Real.exp (∑ p : P, J p) * typedESZ ends rho ∅ := by
    simpa [rho, multibondTwistCoupling] using hden0
  rw [hnum, hden]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]
  exact typedESZ_div_eq_consistencyMass ends rho D


theorem cubicalXYWilsonExpectation_eq_typedFKConsistencyMass
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      typedFKEventMass cubicalDualEnds
        (fun p => 1 - Real.exp (-2 * gaugeDualCoupling (K p)))
        (typedFKConsistencyEvent cubicalDualEnds (cubicalXYSheet k)) := by
  rw [cubicalXYWilsonExpectation_eq_twistedIsingPartitionRatio
    ha hb hc k K hK]
  exact multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass
    cubicalDualEnds (fun p => gaugeDualCoupling (K p)) (cubicalXYSheet k)


end
end StatMech.FrontierA
