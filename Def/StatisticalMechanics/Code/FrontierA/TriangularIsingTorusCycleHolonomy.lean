/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


def triangularIntStep : Fin 6 -> Int × Int :=
  ![(-1, 0), (1, 0), (0, -1), (0, 1), (-1, -1), (1, 1)]


def triangularIntPos {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6) (k : Fin n) : Int × Int :=
  ∑ i ∈ Finset.univ.filter (· < k), triangularIntStep (direction i)

end StatMech.FrontierA
