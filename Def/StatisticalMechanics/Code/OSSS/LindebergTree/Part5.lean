/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Analytic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def freshAt (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) : ℝ :=
  if e ∈ pathPrefix T ω (t + 1) ∧ e ∉ pathPrefix T ω t then (1 : ℝ) else 0


noncomputable def revealmentMu (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (e : E) : ℝ :=
  mean μ (fun ω => if e ∈ T.queried ω then (1 : ℝ) else 0)


end Analytic
end LindebergTree
end OSSS
end StatMech
