/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part2
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def codePrefix (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) : ℕ → ConfigSpace E
  | 0 => fun _ => false
  | (k+1) =>
      let prev := codePrefix μ σ u k
      if hk : k < n then
        Function.update prev (σ ⟨k, hk⟩)
          (decide (u ⟨k, hk⟩ ≥ condProbClosed μ (prefixSet σ k) prev (σ ⟨k, hk⟩)))
      else prev


noncomputable def codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u : Fin n → ℝ) : ConfigSpace E :=
  codePrefix μ σ u n


end OSSS.Coding
end StatMech
