/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_whynotperedge
import Theorem.StatisticalMechanics.Code.Walls.oc3_noproductweight
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

open StatMech.OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


def oc3_GenuinelyCorrelated (μ : ConfigSpace E → ℝ) : Prop :=
  ∃ e e' : E, e ≠ e' ∧ Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0


end Walls
end StatMech
