/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
import Def.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instDecidableRelFKRectInducedGraph
    (R : FKRectTorus) (S : Set R.Vertex) :
    DecidableRel (fkRectInducedGraph R S).Adj := Classical.decRel _

noncomputable instance instDecidableRelFKRectInducedOuterGraph
    (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

end
end StatMech.FrontierD
