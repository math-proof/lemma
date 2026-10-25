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
import Def.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection


namespace StatMech.FrontierD

noncomputable section

abbrev FKRectRightStripVertex (R : FKRectTorus) (cut : Nat) :=
  FKRectInducedVertex R (fkRectRightStrip R cut)

abbrev FKRectRightStripBandVertex (R : FKRectTorus)
    (cut lower upper : Nat) :=
  FKRectInducedVertex R (fkRectRightStripBand R cut lower upper)


end
end StatMech.FrontierD
