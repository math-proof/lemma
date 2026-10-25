/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part5
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


def StepCovBound (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (e : E),
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      ≤ Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshAt T ω t e)


end Analytic
end LindebergTree
end OSSS
end StatMech
