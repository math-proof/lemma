/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part6
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectGraphEdgesOfIndices (R : FKRectTorus)
    (I : Finset R.EdgeIndex) :
    Finset {e // e ∈ (fkRectTorusGraph R).edgeSet} :=
  I.map (fkRectEdgeGraphEquiv R).toEmbedding

end
end StatMech.FrontierD
