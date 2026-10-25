/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology
open scoped BigOperators


namespace StatMech.FrontierA

def triangularIntVector (a : Fin 6) : Complex :=
  triangularIntPoint (triangularIntStep a)

end StatMech.FrontierA
