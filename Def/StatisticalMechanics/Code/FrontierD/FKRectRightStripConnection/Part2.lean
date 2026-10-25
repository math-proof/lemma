/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection


namespace StatMech.FrontierD

noncomputable section

def fkRectIndexedPatternEvent (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (eta : R.Configuration) :
    Set R.Configuration :=
  {omega | ∀ a ∈ I, omega a = eta a}

end
end StatMech.FrontierD
