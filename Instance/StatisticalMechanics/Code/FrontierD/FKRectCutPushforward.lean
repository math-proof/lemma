/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

instance fkRectCutPushforwardDecidableRel (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

instance fkRectCutPushforwardEdgeFintype (R : FKRectTorus) :
    Fintype {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  (fkRectTorusGraph R).fintypeEdgeSet

instance fkRectCutPushforwardConfigurationFintype (R : FKRectTorus) :
    Fintype (FKRectGraphConfiguration R) :=
  Pi.instFintype


end
end StatMech.FrontierD
