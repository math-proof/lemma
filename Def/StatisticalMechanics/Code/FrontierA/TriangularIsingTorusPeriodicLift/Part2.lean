/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicLift
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def triangularTorusCycleNativeDart
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root)
    (k : Fin p.darts.length) : triangularTorusDart L :=
  (triangularTorusDartEquiv L).symm (kwGraphCycleDartLoop p k)

end StatMech.FrontierA
