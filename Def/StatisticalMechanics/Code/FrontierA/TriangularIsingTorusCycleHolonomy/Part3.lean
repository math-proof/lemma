/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


def triangularCanonicalStep : Fin 3 -> Int × Int :=
  ![(1, 0), (0, 1), (1, 1)]

def triangularCanonicalKind : Fin 6 -> Fin 3 :=
  ![0, 0, 1, 1, 2, 2]

def triangularCanonicalBase
    (p : Int × Int) : Fin 6 -> Int × Int :=
  ![p + (-1, 0), p, p + (0, -1), p, p + (-1, -1), p]

end StatMech.FrontierA
