/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc2_covedgeascube
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc2_codinglawsingle
import Theorem.StatisticalMechanics.Code.Walls.oc2_coordreadmatch
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding

open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def oc2_cubeCovSum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ e, oc2_cubeCov μ σ f (CovLowerBound.coordI e)


end Walls
end StatMech
