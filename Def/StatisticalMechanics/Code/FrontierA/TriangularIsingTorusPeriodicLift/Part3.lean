/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicLift.Part2
open scoped BigOperators


namespace StatMech.FrontierA

def triangularIntPeriodicPos
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (z : Int × Fin n) : Int × Int :=
  let displacement := ∑ k, triangularIntStep (direction k)
  (z.1 * displacement.1 + (triangularIntPos direction z.2).1,
    z.1 * displacement.2 + (triangularIntPos direction z.2).2)

end StatMech.FrontierA
