/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectInducedConditionalLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreConditionalLowerProduct
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectFullGraphEvent (R : FKRectTorus)
    (B : Set R.Configuration) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  FK.ecz_closeOff (fkRectTorusGraph R) ⁻¹' fkRectFullEdgeEvent R B


end
end StatMech.FrontierD
