/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_noproductweight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc2_thetamatch.Part2
import Theorem.StatisticalMechanics.Code.Walls.oc3_noproductweight.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
import Theorem.StatisticalMechanics.Code.Walls.oc4_noproductweight
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

open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def oc4_posCorrMu : ConfigSpace (Fin 2) → ℝ :=
  fun ω => if ω 0 = ω 1 then (2 : ℝ) / 5 else (1 : ℝ) / 10


end Walls
end StatMech
