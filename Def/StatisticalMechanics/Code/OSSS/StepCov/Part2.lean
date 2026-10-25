/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Theorem.StatisticalMechanics.Code.OSSS.StepCov.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree

open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


def StepCovResidue (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (e : E) : Prop :=
  ∀ F ∈ prefSet e,
    mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
        * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω)))
      ≤ Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshPI T ω t e F)


def StepCovBoundTwo (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (e : E),
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      ≤ 2 * (Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshAt T ω t e))


end StepCov
end OSSS
end StatMech
