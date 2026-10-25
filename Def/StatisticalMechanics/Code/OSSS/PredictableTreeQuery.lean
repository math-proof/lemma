/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PredictableTreeQuery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace OSSS

namespace PredictableTreeQuery

open DecisionTree LindebergTree

variable {E : Type*} [Fintype E] [DecidableEq E]


def pathQuery : DecisionTree E → ConfigSpace E → ℕ → Option E
  | .leaf _, _, _ => none
  | .node e _ _, _, 0 => some e
  | .node e l r, ω, t + 1 => pathQuery (if ω e then l else r) ω t


end PredictableTreeQuery
end OSSS
end StatMech
