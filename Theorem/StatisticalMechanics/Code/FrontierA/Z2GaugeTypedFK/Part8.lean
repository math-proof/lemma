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
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part10
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem card_typedSignedCompatible_empty
    (ends : P -> V × V) (omega : P -> Bool) :
    Nat.card {sigma : V -> Bool // TypedSignedCompatible ends ∅ omega sigma} =
      2 ^ typedNumClusters ends omega := by
  classical
  rw [Nat.card_congr (typedConstOnOpenEquiv ends omega).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool]
  simp [typedNumClusters, Nat.card_eq_fintype_card]

theorem typedFKWeight_eq_activity_mul_clusters
    (ends : P -> V × V) (rho : P -> Real) (omega : P -> Bool) :
    typedFKWeight ends rho omega =
      typedESActivity rho omega * (2 : Real) ^ typedNumClusters ends omega := by
  unfold typedFKWeight
  rw [typedESWeight_sum_sigma_eq_activity_mul_card]
  congr 1
  have hcard := card_typedSignedCompatible_empty ends omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  rw [hcard]
  push_cast
  rfl

theorem typedESActivity_logModular (rho : P -> Real) (a b : P -> Bool) :
    typedESActivity rho a * typedESActivity rho b =
      typedESActivity rho (a ⊔ b) * typedESActivity rho (a ⊓ b) := by
  unfold typedESActivity
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  cases ha : a p <;> cases hb : b p <;>
    simp [ha, hb, mul_comm]

theorem typedFKWeight_logSupermodular
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (a b : P -> Bool) :
    typedFKWeight ends rho a * typedFKWeight ends rho b <=
      typedFKWeight ends rho (a ⊔ b) * typedFKWeight ends rho (a ⊓ b) := by
  have hcluster :
      (2 : Real) ^ typedNumClusters ends a *
          (2 : Real) ^ typedNumClusters ends b <=
        (2 : Real) ^ typedNumClusters ends (a ⊔ b) *
          (2 : Real) ^ typedNumClusters ends (a ⊓ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num)
      (typedNumClusters_supermodular ends a b)
  have hactivity := typedESActivity_logModular rho a b
  have hnonneg : 0 <= typedESActivity rho a * typedESActivity rho b := by
    apply mul_nonneg
    · unfold typedESActivity
      apply Finset.prod_nonneg
      intro p _
      cases hp : a p <;> simp [hrho0 p, sub_nonneg.mpr (hrho1 p)]
    · unfold typedESActivity
      apply Finset.prod_nonneg
      intro p _
      cases hp : b p <;> simp [hrho0 p, sub_nonneg.mpr (hrho1 p)]
  simp_rw [typedFKWeight_eq_activity_mul_clusters]
  calc
    (typedESActivity rho a * 2 ^ typedNumClusters ends a) *
        (typedESActivity rho b * 2 ^ typedNumClusters ends b) =
      (typedESActivity rho a * typedESActivity rho b) *
        (2 ^ typedNumClusters ends a * 2 ^ typedNumClusters ends b) := by ring
    _ <= (typedESActivity rho a * typedESActivity rho b) *
        (2 ^ typedNumClusters ends (a ⊔ b) *
          2 ^ typedNumClusters ends (a ⊓ b)) :=
      mul_le_mul_of_nonneg_left hcluster hnonneg
    _ = (typedESActivity rho (a ⊔ b) *
          2 ^ typedNumClusters ends (a ⊔ b)) *
        (typedESActivity rho (a ⊓ b) *
          2 ^ typedNumClusters ends (a ⊓ b)) := by rw [hactivity]; ring


theorem typedFKProb_FKGLatticeCondition
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho) :
    FKGLatticeCondition (typedFKProb ends rho) := by
  intro a b
  simp only [typedFKProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZ hZ)).mpr
    (typedFKWeight_logSupermodular ends hrho0 hrho1 a b)


theorem typedFKProb_positively_associated
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho)
    {f g : (P -> Bool) -> Real} (hf : Monotone f) (hg : Monotone g) :
    (∑ omega, typedFKProb ends rho omega * f omega) *
        (∑ omega, typedFKProb ends rho omega * g omega) <=
      ∑ omega, typedFKProb ends rho omega * (f omega * g omega) := by
  exact fkg_inequality
    (fun omega => typedFKProb_nonneg_of_nonneg
      ends hrho0 hrho1 hZ omega)
    (typedFKProb_sum_eq_one ends rho hZ.ne')
    (typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ) hf hg


theorem typedFKProb_positively_associated_events
    (ends : P -> V × V) {rho : P -> Real}
    (hrho0 : forall p, 0 <= rho p) (hrho1 : forall p, rho p <= 1)
    (hZ : 0 < typedFKZ ends rho)
    {A B : Set (P -> Bool)} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    typedFKEventMass ends rho A * typedFKEventMass ends rho B <=
      typedFKEventMass ends rho (A ∩ B) := by
  exact fkg_inequality_events
    (fun omega => typedFKProb_nonneg_of_nonneg
      ends hrho0 hrho1 hZ omega)
    (typedFKProb_sum_eq_one ends rho hZ.ne')
    (typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ) hA hB


theorem typedOpenGraph_mono (ends : P -> V × V)
    {a b : P -> Bool} (hab : a <= b) :
    typedOpenGraph ends a <= typedOpenGraph ends b := by
  intro x y hxy
  obtain ⟨p, hp, hends, hne⟩ := hxy
  have hbp : b p = true := by
    have := hab p
    rw [hp] at this
    cases hbp : b p
    · exfalso
      rw [hbp] at this
      exact (by decide : ¬ (true : Bool) <= false) this
    · rfl
  exact ⟨p, hbp, hends, hne⟩


end
end StatMech.FrontierA
