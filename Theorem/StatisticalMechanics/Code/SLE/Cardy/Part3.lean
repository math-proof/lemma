/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy.Part3
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma cardyPrefactor_pos : 0 < cardyPrefactor := by
  unfold cardyPrefactor
  have h1 : (0 : ℝ) < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  apply div_pos
  · positivity
  · positivity


@[simp] lemma cardyCrossing_zero : cardyCrossing 0 = 0 := by
  unfold cardyCrossing
  rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 3 ≠ 0)]
  ring


end StatMech.SLE
