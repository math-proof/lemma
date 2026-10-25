/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusCrossingEvents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectConnectedWithin (R : FKRectTorus) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) : Prop :=
  ((fkRectOpenGraph R omega).induce S).Reachable x y


end
end StatMech.FrontierD
