/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Theorem.StatisticalMechanics.Code.OSSS.StepCov
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


noncomputable def freshPI (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E)
    (F : Finset E) : ℝ :=
  if pathPrefix T ω t = F ∧ pathPrefix T ω (t + 1) = insert e F then (1 : ℝ) else 0


noncomputable def prefSet (e : E) : Finset (Finset E) :=
  Finset.univ.filter (fun F => e ∉ F)


end StepCov
end OSSS
end StatMech
