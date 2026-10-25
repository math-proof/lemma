/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def triangularIntReduce (L : Nat) : Int × Int -> ZMod L × ZMod L :=
  fun p => ((p.1 : ZMod L), (p.2 : ZMod L))

end StatMech.FrontierA
