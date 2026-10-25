/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part4
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def codeFibre (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) : Set (Fin n → ℝ) :=
  {u | (∀ t, u t ∈ Set.Ico (0 : ℝ) 1) ∧ codeMap μ (σ : Fin n → E) u = x}


end OSSS.Coding
end StatMech
