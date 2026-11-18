/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.Group
public import Def.v1.Atlas.TensorCategories.code.GradedVec.Part5
public import Instance.v1.Atlas.TensorCategories.code.GradedVec.Part3
@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Rigidity

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

private lemma NormalizedGroupCocycle3.normalized_right (g h : G) :
    ω.toFun g h 1 = 1 := by
  have hc := ω.cocycle_cond g h 1 1
  simp only [mul_one] at hc
  rw [ω.normalized (g * h) 1, ω.normalized h 1] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun g h 1 * ω.toFun g h 1 = ω.toFun g h 1 * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

private lemma NormalizedGroupCocycle3.normalized_left (g h : G) :
    ω.toFun 1 g h = 1 := by
  have hc := ω.cocycle_cond 1 1 g h
  simp only [one_mul] at hc
  rw [ω.normalized 1 (g * h), ω.normalized 1 g] at hc
  simp only [one_mul, mul_one] at hc
  have : ω.toFun 1 g h * ω.toFun 1 g h = ω.toFun 1 g h * 1 := by
    rw [mul_one]; exact hc.symm
  exact mul_left_cancel this

private lemma NormalizedGroupCocycle3.cocycle_inv_cancel (g : G) :
    ω.toFun g g⁻¹ g * ω.toFun g⁻¹ g g⁻¹ = 1 := by
  have hc := ω.cocycle_cond g g⁻¹ g g⁻¹
  simp only [mul_inv_cancel, inv_mul_cancel] at hc
  rw [ω.normalized_left g g⁻¹, ω.normalized_right g g⁻¹, ω.normalized g g⁻¹] at hc
  simp only [mul_one] at hc
  exact hc.symm

/-- Each object `X` of `CG G A ω` has an exact pairing with its dual
`Xᘁ = ⟨g⁻¹⟩`, exhibiting `CG G A ω` as a rigid monoidal category. -/
noncomputable instance CG.exactPairing (X : CG G A ω) :
    ExactPairing X (CG.dualObj X) where
  coevaluation' := CG.coevMorphism X
  evaluation' := CG.evalMorphism X
  coevaluation_evaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * ((ω.toFun X.val⁻¹ X.val X.val⁻¹)⁻¹ *
      ((ω.toFun X.val X.val⁻¹ X.val)⁻¹ * 1)) = 1 * 1
    simp only [one_mul, mul_one]
    rw [← mul_inv]
    rw [inv_eq_one]
    have := ω.cocycle_inv_cancel X.val
    rw [mul_comm] at this
    exact this
  evaluation_coevaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * (ω.toFun X.val X.val⁻¹ X.val *
      (1 * (ω.toFun X.val X.val⁻¹ X.val)⁻¹)) = 1 * 1
    simp [mul_inv_cancel]

end Rigidity
