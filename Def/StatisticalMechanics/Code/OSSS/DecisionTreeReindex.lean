/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/DecisionTreeReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6


namespace StatMech

namespace OSSS

open DecisionTree

variable {I E : Type*}


def restrictConfig (iota : I -> E) (omega : ConfigSpace E) : ConfigSpace I :=
  fun i => omega (iota i)

namespace DecisionTree


def reindex (iota : I -> E) : DecisionTree I -> DecisionTree E
  | .leaf b => .leaf b
  | .node i t f => .node (iota i) (reindex iota t) (reindex iota f)

end DecisionTree
end OSSS
end StatMech
