/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc4_scalesum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentSum
import Theorem.StatisticalMechanics.Code.Walls.oc3_core
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding

open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def oc4_codingProb {α : Type*} (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (g : α → ℕ → ConfigSpace E → ℝ) (x : α) (j : ℕ) : ℝ :=
  ∫ u, g x j (codeMap μ σ u) ∂(Vcube n)


end Walls
end StatMech
