module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
public import Theorem.StatisticalMechanics.Code.FK.PositiveAssociation
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open StatMech

instance fkRectTorusGraphDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _


end
end StatMech.FrontierD
