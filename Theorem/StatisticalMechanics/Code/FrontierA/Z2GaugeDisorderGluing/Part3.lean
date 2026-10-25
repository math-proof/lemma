/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


section DisjointBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]


theorem multibondIsingAction_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : V₁ → Bool) (s₂ : V₂ → Bool) :
    multibondIsingAction (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) =
      multibondIsingAction ends₁ J₁ s₁ +
        multibondIsingAction ends₂ J₂ s₂ := by
  unfold multibondIsingAction
  rw [Fintype.sum_sum_type]
  congr 1


theorem multibondIsingWeight_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : V₁ → Bool) (s₂ : V₂ → Bool) :
    multibondIsingWeight (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂)) =
      multibondIsingWeight ends₁ J₁ s₁ *
        multibondIsingWeight ends₂ J₂ s₂ := by
  change Real.exp (multibondIsingAction (multibondSumEnds ends₁ ends₂)
      (multibondSumCoupling J₁ J₂)
      ((Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm (s₁, s₂))) =
    Real.exp (multibondIsingAction ends₁ J₁ s₁) *
      Real.exp (multibondIsingAction ends₂ J₂ s₂)
  rw [multibondIsingAction_sum, Real.exp_add]


theorem multibondIsingPartition_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    multibondIsingPartition (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) =
      multibondIsingPartition ends₁ J₁ *
        multibondIsingPartition ends₂ J₂ := by
  unfold multibondIsingPartition
  rw [← Equiv.sum_comp (Equiv.sumArrowEquivProdArrow V₁ V₂ Bool).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [multibondIsingWeight_sum]
  rw [Finset.sum_mul_sum]


theorem multibondTwistCoupling_sum
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondTwistCoupling (multibondSumCoupling J₁ J₂)
        (multibondSumSheet D₁ D₂) =
      multibondSumCoupling (multibondTwistCoupling J₁ D₁)
        (multibondTwistCoupling J₂ D₂) := by
  funext p
  cases p <;> simp [multibondTwistCoupling, multibondSumCoupling,
    multibondSumSheet]


theorem multibondDisorderFreeEnergy_sum
    (ends₁ : P₁ → V₁ × V₁) (ends₂ : P₂ → V₂ × V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondDisorderFreeEnergy (multibondSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) =
      multibondDisorderFreeEnergy ends₁ J₁ D₁ +
        multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
  unfold multibondDisorderFreeEnergy
  rw [multibondIsingPartition_sum]
  rw [multibondTwistCoupling_sum]
  rw [multibondIsingPartition_sum]
  rw [Real.log_mul
    (multibondIsingPartition_pos ends₁ J₁).ne'
    (multibondIsingPartition_pos ends₂ J₂).ne']
  rw [Real.log_mul
    (multibondIsingPartition_pos ends₁ (multibondTwistCoupling J₁ D₁)).ne'
    (multibondIsingPartition_pos ends₂ (multibondTwistCoupling J₂ D₂)).ne']
  ring

end DisjointBlocks
end
end StatMech.FrontierA
