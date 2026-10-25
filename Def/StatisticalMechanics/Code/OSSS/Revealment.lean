/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Revealment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Revealment

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def revealment (ν : E → Bool → ℝ) (T : DecisionTree E) (e : E) : ℝ :=
  reveal ν T e

end Revealment
end OSSS
end StatMech
