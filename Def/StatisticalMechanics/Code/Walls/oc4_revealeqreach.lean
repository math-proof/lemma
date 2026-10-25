/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_revealeqreach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
open scoped BigOperators
open MeasureTheory Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.AdaptMConditional

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def oc4_notDetProb (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ X, (if detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) then (0 : ℝ) else 1) * μ X


end Walls
end StatMech
