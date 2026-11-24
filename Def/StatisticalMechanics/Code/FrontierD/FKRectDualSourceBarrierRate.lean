module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceBarrierRate
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectDualPullbackSourceLeftBarrier (R : FKRectTorus)
    (leftRight : Nat) (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectDualPreimageEvent R (fkRectSourceLeftBarrier R leftRight gap)

end
end StatMech.FrontierD
