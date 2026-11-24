module
public import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
public import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part4
open scoped BigOperators
open Finset MeasureTheory
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def codeFibre (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) : Set (Fin n → ℝ) :=
  {u | (∀ t, u t ∈ Set.Ico (0 : ℝ) 1) ∧ codeMap μ (σ : Fin n → E) u = x}


end OSSS.Coding
end StatMech
