/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
import Instance.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding


namespace StatMech.FrontierA

open SimpleGraph

def triangularTorusSplitOffset : Fin 6 -> Nat × Nat :=
  ![(0, 1), (2, 1), (1, 0), (1, 2), (0, 0), (2, 2)]

end StatMech.FrontierA
