/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc3_vcubeprob
open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc3_siteSum (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) :
    ∑ b, ENNReal.ofReal (ν e b) = 1 := by
  rw [Fintype.sum_bool, add_comm,
      ← ENNReal.ofReal_add (hν.nonneg e false) (hν.nonneg e true), hν.normalized e]
  simp


end Walls
end StatMech
