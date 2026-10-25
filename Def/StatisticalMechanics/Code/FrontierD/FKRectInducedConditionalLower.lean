/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectInducedVertex (R : FKRectTorus) (S : Set R.Vertex) := S

end
end StatMech.FrontierD
