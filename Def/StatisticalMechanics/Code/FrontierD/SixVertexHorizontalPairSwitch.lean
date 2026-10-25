/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexSwitchHorizontalPair
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (fun v => if mask v.1 then horizontal.2 v else horizontal.1 v,
   fun v => if mask v.1 then horizontal.1 v else horizontal.2 v)

end
end StatMech.FrontierD
