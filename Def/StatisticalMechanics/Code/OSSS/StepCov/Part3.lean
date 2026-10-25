/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Theorem.StatisticalMechanics.Code.OSSS.StepCov.Part3
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


namespace Counterexample

noncomputable def muU : ConfigSpace Bool → ℝ := fun _ => 1 / 4


def Tw : DecisionTree Bool := DecisionTree.node false (DecisionTree.leaf true) (DecisionTree.leaf false)


noncomputable def fAvg : ConfigSpace Bool → ℝ := fun ω =>
  (if ω false then (1:ℝ) else 0) * (1 / 2) + (if ω true then (1:ℝ) else 0) * (1 / 2)

end Counterexample
end StepCov
end OSSS
end StatMech
