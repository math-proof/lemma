/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part3
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


section RootedBlocks

variable {P₁ P₂ V₁ V₂ : Type*}
  [Fintype P₁] [DecidableEq P₁] [Fintype P₂] [DecidableEq P₂]
  [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]


@[simp] theorem rootedSumAnchoredEquiv_symm_apply_inl
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) (q : Option V₁) :
    ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1
        (rootedSumInl q) = s₁.1 q := by
  cases q <;> simp [rootedSumAnchoredEquiv, rootedSumInl, s₁.2]

@[simp] theorem rootedSumAnchoredEquiv_symm_apply_inr
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) (q : Option V₂) :
    ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1
        (rootedSumInr q) = s₂.1 q := by
  cases q <;> simp [rootedSumAnchoredEquiv, rootedSumInr, s₂.2]


theorem multibondIsingAction_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) :
    multibondIsingAction (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 =
      multibondIsingAction ends₁ J₁ s₁.1 +
        multibondIsingAction ends₂ J₂ s₂.1 := by
  unfold multibondIsingAction
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro p _
    simp only [multibondRootedSumEnds, multibondSumCoupling, Sum.elim_inl,
      rootedSumAnchoredEquiv_symm_apply_inl]
  · apply Finset.sum_congr rfl
    intro p _
    simp only [multibondRootedSumEnds, multibondSumCoupling, Sum.elim_inr,
      rootedSumAnchoredEquiv_symm_apply_inr]


theorem multibondIsingWeight_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (s₁ : AnchoredConfig (Option V₁) none)
    (s₂ : AnchoredConfig (Option V₂) none) :
    multibondIsingWeight (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂)
        ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1 =
      multibondIsingWeight ends₁ J₁ s₁.1 *
        multibondIsingWeight ends₂ J₂ s₂.1 := by
  change Real.exp (multibondIsingAction (multibondRootedSumEnds ends₁ ends₂)
      (multibondSumCoupling J₁ J₂)
      ((rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm (s₁, s₂)).1) =
    Real.exp (multibondIsingAction ends₁ J₁ s₁.1) *
      Real.exp (multibondIsingAction ends₂ J₂ s₂.1)
  rw [multibondIsingAction_rootedSum, Real.exp_add]


theorem multibondIsingPartition_eq_two_mul_anchoredWeight
    {Q W : Type*} [Fintype Q] [DecidableEq Q] [Fintype W] [DecidableEq W]
    (root : W) (ends : Q → W × W) (J : Q → Real) :
    multibondIsingPartition ends J =
      2 * ∑ s : AnchoredConfig W root, multibondIsingWeight ends J s.1 := by
  rw [multibondIsingPartition_eq_two_mul_anchored]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact (multibondIsingWeight_eq_activity ends J s.1).symm


theorem two_mul_multibondIsingPartition_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real) :
    2 * multibondIsingPartition (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) =
      multibondIsingPartition ends₁ J₁ *
        multibondIsingPartition ends₂ J₂ := by
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none]
  rw [← Equiv.sum_comp
    (rootedSumAnchoredEquiv (V₁ := V₁) (V₂ := V₂)).symm]
  rw [Fintype.sum_prod_type]
  simp_rw [multibondIsingWeight_rootedSum]
  rw [← Finset.sum_mul_sum]
  rw [multibondIsingPartition_eq_two_mul_anchoredWeight none,
    multibondIsingPartition_eq_two_mul_anchoredWeight none]
  ring


theorem multibondDisorderFreeEnergy_rootedSum
    (ends₁ : P₁ → Option V₁ × Option V₁)
    (ends₂ : P₂ → Option V₂ × Option V₂)
    (J₁ : P₁ → Real) (J₂ : P₂ → Real)
    (D₁ : Finset P₁) (D₂ : Finset P₂) :
    multibondDisorderFreeEnergy (multibondRootedSumEnds ends₁ ends₂)
        (multibondSumCoupling J₁ J₂) (multibondSumSheet D₁ D₂) =
      multibondDisorderFreeEnergy ends₁ J₁ D₁ +
        multibondDisorderFreeEnergy ends₂ J₂ D₂ := by
  have hordinary := two_mul_multibondIsingPartition_rootedSum
    ends₁ ends₂ J₁ J₂
  have htwisted := two_mul_multibondIsingPartition_rootedSum ends₁ ends₂
    (multibondTwistCoupling J₁ D₁) (multibondTwistCoupling J₂ D₂)
  rw [← multibondTwistCoupling_sum J₁ J₂ D₁ D₂] at htwisted
  have hordLog := congrArg Real.log hordinary
  have htwLog := congrArg Real.log htwisted
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (multibondIsingPartition_pos _ _).ne',
    Real.log_mul (multibondIsingPartition_pos ends₁ J₁).ne'
      (multibondIsingPartition_pos ends₂ J₂).ne'] at hordLog
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (multibondIsingPartition_pos _ _).ne',
    Real.log_mul
      (multibondIsingPartition_pos ends₁ (multibondTwistCoupling J₁ D₁)).ne'
      (multibondIsingPartition_pos ends₂ (multibondTwistCoupling J₂ D₂)).ne'] at htwLog
  unfold multibondDisorderFreeEnergy
  linarith

end RootedBlocks
end
end StatMech.FrontierA
