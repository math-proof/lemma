/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part3
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_ExplorationKernel

variable {D E : Type*} [Preorder D] [DecidableEq E]


@[simp] theorem weight_nil (K : shb_ExplorationKernel D E) (d : D) :
    K.weight d [] = 1 := rfl

@[simp] theorem weight_cons (K : shb_ExplorationKernel D E)
    (d : D) (e : E) (es : List E) :
    K.weight d (e :: es) =
      K.amplitude d e * K.weight (K.exploration.advance d e) es := rfl


theorem weight_nonneg (K : shb_ExplorationKernel D E) (d : D) (p : List E) :
    0 ≤ K.weight d p := by
  induction p generalizing d with
  | nil => exact zero_le_one
  | cons e p ih =>
      exact mul_nonneg (K.amplitude_nonneg d e)
        (ih (K.exploration.advance d e))


theorem weight_append (K : shb_ExplorationKernel D E)
    (d : D) (p q : List E) :
    K.weight d (p ++ q) =
      K.weight d p * K.weight (K.exploration.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, weight_cons,
        shb_DynamicEdgeExploration.residual_cons, ih]
      ring


theorem residual_mono (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.exploration.residual small p ≤ K.exploration.residual large p := by
  induction p generalizing small large with
  | nil => exact h
  | cons e p ih =>
      exact ih (K.advance_mono h e)


theorem weight_antitone (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.weight large p ≤ K.weight small p := by
  induction p generalizing small large with
  | nil => exact le_rfl
  | cons e p ih =>
      exact mul_le_mul (K.amplitude_antitone h e)
        (ih (K.advance_mono h e))
        (K.weight_nonneg _ _) (K.amplitude_nonneg _ _)

end shb_ExplorationKernel
end StatMech.Sharpness
