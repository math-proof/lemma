/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Path

variable {E : Type*} [DecidableEq E]


def treeDepth : DecisionTree E → ℕ
  | leaf _ => 0
  | node _ t f => max (treeDepth t) (treeDepth f) + 1

end Path
end LindebergTree
end OSSS
end StatMech
