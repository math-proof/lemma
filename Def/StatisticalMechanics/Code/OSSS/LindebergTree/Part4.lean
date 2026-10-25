/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part3
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


noncomputable def meanAbs (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, |g ω| * μ ω


end Analytic
end LindebergTree
end OSSS
end StatMech
