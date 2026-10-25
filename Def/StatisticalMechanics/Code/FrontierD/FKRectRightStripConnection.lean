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


namespace StatMech.FrontierD

noncomputable section

def fkRectRightStrip (R : FKRectTorus) (cut : Nat) : Set R.Vertex :=
  {v | cut ≤ v.1.val}


def fkRectRightStripBand (R : FKRectTorus)
    (cut lower upper : Nat) : Set R.Vertex :=
  {v | cut ≤ v.1.val ∧ lower ≤ v.2.val ∧ v.2.val ≤ upper}

end
end StatMech.FrontierD
