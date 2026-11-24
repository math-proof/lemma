module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def fkRectEdgeGraphEquiv (R : FKRectTorus) :
    R.EdgeIndex ≃ {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  Equiv.ofBijective (fkRectEdgeToGraphEdge R)
    (fkRectEdgeToGraphEdge_bijective R)

end
end StatMech.FrontierD
