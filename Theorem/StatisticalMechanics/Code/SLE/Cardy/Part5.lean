/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy.Part5
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma sleDimension_apply (κ : ℝ) : sleDimension κ = 1 + κ / 8 := rfl


@[simp] lemma sleDimension_zero : sleDimension 0 = 1 := by simp [sleDimension]


@[simp] lemma sleDimension_eight : sleDimension 8 = 2 := by norm_num [sleDimension]


lemma sleDimension_mem_Icc {κ : ℝ} (h0 : 0 ≤ κ) (h8 : κ ≤ 8) :
    sleDimension κ ∈ Set.Icc (1 : ℝ) 2 := by
  constructor <;> simp only [sleDimension] <;> linarith


lemma sleDimension_strictMono : StrictMono sleDimension := by
  intro a b hab
  simp only [sleDimension]
  linarith


end StatMech.SLE
