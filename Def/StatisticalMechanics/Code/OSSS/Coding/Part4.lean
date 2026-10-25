/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part3
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def thr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E) (x : ConfigSpace E)
    (t : Fin n) : ℝ :=
  condProbClosed μ (prefixSet σ (t : ℕ)) x (σ t)


noncomputable def codeInterval (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : Set ℝ :=
  if x (σ t) then Set.Ico (thr μ σ x t) 1 else Set.Ico (0 : ℝ) (thr μ σ x t)


end OSSS.Coding
end StatMech
