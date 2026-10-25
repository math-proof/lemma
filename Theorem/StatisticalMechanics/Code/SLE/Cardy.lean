/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma crossRatio_def {K : Type*} [Field K] (z₁ z₂ z₃ z₄ : K) :
    crossRatio z₁ z₂ z₃ z₄ = (z₁ - z₃) * (z₂ - z₄) / ((z₁ - z₄) * (z₂ - z₃)) := rfl


@[simp] lemma crossRatio_self_left_third {K : Type*} [Field K]
    (z z₂ z₄ : K) : crossRatio z z₂ z z₄ = 0 := by
  simp [crossRatio]


@[simp] lemma crossRatio_self_second_fourth {K : Type*} [Field K]
    (z₁ z z₃ : K) : crossRatio z₁ z z₃ z = 0 := by
  simp [crossRatio]


lemma crossRatio_eq_one_of_third_eq_fourth {K : Type*} [Field K]
    {z₁ z₂ z₃ z₄ : K} (h : z₃ = z₄) (h₁ : z₁ - z₄ ≠ 0) (h₂ : z₂ - z₃ ≠ 0) :
    crossRatio z₁ z₂ z₃ z₄ = 1 := by
  subst h
  rw [crossRatio]
  exact div_self (mul_ne_zero h₁ h₂)


end StatMech.SLE
