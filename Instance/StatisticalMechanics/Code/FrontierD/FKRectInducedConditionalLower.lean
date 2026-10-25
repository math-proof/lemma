/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
import Def.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instFintypeFKRectInducedVertex
    (R : FKRectTorus) (S : Set R.Vertex) :
    Fintype (FKRectInducedVertex R S) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instDecidableEqFKRectInducedVertex
    (R : FKRectTorus) (S : Set R.Vertex) :
    DecidableEq (FKRectInducedVertex R S) := Classical.decEq _


end
end StatMech.FrontierD
